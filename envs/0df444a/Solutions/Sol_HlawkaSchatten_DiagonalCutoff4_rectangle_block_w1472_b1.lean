-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1472_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:10:57.555981+00:00
-- url     : https://prove2.me/submissions/1b48faef-0efa-485f-be6c-9b105324335d

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
theorem support_rectangle_w1472_s3_0 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2409963/12500000 : ℝ)*x 0 + (680455183/1250000000 : ℝ)*x 1 + (1042143731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2409963/12500000 : ℝ)^4441 ≤ (11772280752207/100000000000000 : ℝ)^3417 := by
    have hnat : (2409963 : ℕ)^4441*100000000000000^3417 ≤ 11772280752207^3417*12500000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409963 12500000 11772280752207 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680455183/1250000000 : ℝ)^4441 ≤ (45367138764397/100000000000000 : ℝ)^3417 := by
    have hnat : (680455183 : ℕ)^4441*100000000000000^3417 ≤ 45367138764397^3417*1250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680455183 1250000000 45367138764397 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042143731/2000000000 : ℝ)^4441 ≤ (267878627879/625000000000 : ℝ)^3417 := by
    have hnat : (1042143731 : ℕ)^4441*625000000000^3417 ≤ 267878627879^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042143731 2000000000 267878627879 625000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2409963/12500000 : ℝ), (680455183/1250000000 : ℝ), (1042143731/2000000000 : ℝ)] ![(11772280752207/100000000000000 : ℝ), (45367138764397/100000000000000 : ℝ), (267878627879/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2409963/12500000 : ℝ)|^4441 ≤ (11772280752207/100000000000000 : ℝ)^3417
        have hw : |(-2409963/12500000 : ℝ)|=(2409963/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680455183/1250000000 : ℝ)|^4441 ≤ (45367138764397/100000000000000 : ℝ)^3417
        have hw : |(680455183/1250000000 : ℝ)|=(680455183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042143731/2000000000 : ℝ)|^4441 ≤ (267878627879/625000000000 : ℝ)^3417
        have hw : |(1042143731/2000000000 : ℝ)|=(1042143731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s3_1 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535505333/1000000000 : ℝ)*x 0 + (-1023745741/5000000000 : ℝ)*x 1 + (65133981/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535505333/1000000000 : ℝ)^4441 ≤ (22204973589721/50000000000000 : ℝ)^3417 := by
    have hnat : (535505333 : ℕ)^4441*50000000000000^3417 ≤ 22204973589721^3417*1000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535505333 1000000000 22204973589721 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023745741/5000000000 : ℝ)^4441 ≤ (397796069531/3125000000000 : ℝ)^3417 := by
    have hnat : (1023745741 : ℕ)^4441*3125000000000^3417 ≤ 397796069531^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023745741 5000000000 397796069531 3125000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65133981/125000000 : ℝ)^4441 ≤ (4286057858981/10000000000000 : ℝ)^3417 := by
    have hnat : (65133981 : ℕ)^4441*10000000000000^3417 ≤ 4286057858981^3417*125000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65133981 125000000 4286057858981 10000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535505333/1000000000 : ℝ), (-1023745741/5000000000 : ℝ), (65133981/125000000 : ℝ)] ![(22204973589721/50000000000000 : ℝ), (397796069531/3125000000000 : ℝ), (4286057858981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535505333/1000000000 : ℝ)|^4441 ≤ (22204973589721/50000000000000 : ℝ)^3417
        have hw : |(535505333/1000000000 : ℝ)|=(535505333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023745741/5000000000 : ℝ)|^4441 ≤ (397796069531/3125000000000 : ℝ)^3417
        have hw : |(-1023745741/5000000000 : ℝ)|=(1023745741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65133981/125000000 : ℝ)|^4441 ≤ (4286057858981/10000000000000 : ℝ)^3417
        have hw : |(65133981/125000000 : ℝ)|=(65133981/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s3_2 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355053387/10000000000 : ℝ)*x 0 + (5210718491/10000000000 : ℝ)*x 1 + (-204749139/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355053387/10000000000 : ℝ)^4441 ≤ (2775621737113/6250000000000 : ℝ)^3417 := by
    have hnat : (5355053387 : ℕ)^4441*6250000000000^3417 ≤ 2775621737113^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355053387 10000000000 2775621737113 6250000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5210718491/10000000000 : ℝ)^4441 ≤ (8572115741481/20000000000000 : ℝ)^3417 := by
    have hnat : (5210718491 : ℕ)^4441*20000000000000^3417 ≤ 8572115741481^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210718491 10000000000 8572115741481 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204749139/1000000000 : ℝ)^4441 ≤ (1272947348161/10000000000000 : ℝ)^3417 := by
    have hnat : (204749139 : ℕ)^4441*10000000000000^3417 ≤ 1272947348161^3417*1000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204749139 1000000000 1272947348161 10000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355053387/10000000000 : ℝ), (5210718491/10000000000 : ℝ), (-204749139/1000000000 : ℝ)] ![(2775621737113/6250000000000 : ℝ), (8572115741481/20000000000000 : ℝ), (1272947348161/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355053387/10000000000 : ℝ)|^4441 ≤ (2775621737113/6250000000000 : ℝ)^3417
        have hw : |(5355053387/10000000000 : ℝ)|=(5355053387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5210718491/10000000000 : ℝ)|^4441 ≤ (8572115741481/20000000000000 : ℝ)^3417
        have hw : |(5210718491/10000000000 : ℝ)|=(5210718491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204749139/1000000000 : ℝ)|^4441 ≤ (1272947348161/10000000000000 : ℝ)^3417
        have hw : |(-204749139/1000000000 : ℝ)|=(204749139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s3_3 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072068797/2500000000 : ℝ)*x 0 + (25239739/62500000 : ℝ)*x 1 + (4551677879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072068797/2500000000 : ℝ)^4441 ≤ (1330901174123/4000000000000 : ℝ)^3417 := by
    have hnat : (1072068797 : ℕ)^4441*4000000000000^3417 ≤ 1330901174123^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072068797 2500000000 1330901174123 4000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25239739/62500000 : ℝ)^4441 ≤ (30774645963037/100000000000000 : ℝ)^3417 := by
    have hnat : (25239739 : ℕ)^4441*100000000000000^3417 ≤ 30774645963037^3417*62500000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25239739 62500000 30774645963037 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4551677879/10000000000 : ℝ)^4441 ≤ (8988206166687/25000000000000 : ℝ)^3417 := by
    have hnat : (4551677879 : ℕ)^4441*25000000000000^3417 ≤ 8988206166687^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551677879 10000000000 8988206166687 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072068797/2500000000 : ℝ), (25239739/62500000 : ℝ), (4551677879/10000000000 : ℝ)] ![(1330901174123/4000000000000 : ℝ), (30774645963037/100000000000000 : ℝ), (8988206166687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072068797/2500000000 : ℝ)|^4441 ≤ (1330901174123/4000000000000 : ℝ)^3417
        have hw : |(1072068797/2500000000 : ℝ)|=(1072068797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25239739/62500000 : ℝ)|^4441 ≤ (30774645963037/100000000000000 : ℝ)^3417
        have hw : |(25239739/62500000 : ℝ)|=(25239739/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4551677879/10000000000 : ℝ)|^4441 ≤ (8988206166687/25000000000000 : ℝ)^3417
        have hw : |(4551677879/10000000000 : ℝ)|=(4551677879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s3_4 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-48200131/250000000 : ℝ)*x 0 + (2605980137/5000000000 : ℝ)*x 1 + (2721195199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48200131/250000000 : ℝ)^4441 ≤ (11772557239621/100000000000000 : ℝ)^3417 := by
    have hnat : (48200131 : ℕ)^4441*100000000000000^3417 ≤ 11772557239621^3417*250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48200131 250000000 11772557239621 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2605980137/5000000000 : ℝ)^4441 ≤ (535923180093/1250000000000 : ℝ)^3417 := by
    have hnat : (2605980137 : ℕ)^4441*1250000000000^3417 ≤ 535923180093^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605980137 5000000000 535923180093 1250000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721195199/5000000000 : ℝ)^4441 ≤ (11338397084701/25000000000000 : ℝ)^3417 := by
    have hnat : (2721195199 : ℕ)^4441*25000000000000^3417 ≤ 11338397084701^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721195199 5000000000 11338397084701 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48200131/250000000 : ℝ), (2605980137/5000000000 : ℝ), (2721195199/5000000000 : ℝ)] ![(11772557239621/100000000000000 : ℝ), (535923180093/1250000000000 : ℝ), (11338397084701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48200131/250000000 : ℝ)|^4441 ≤ (11772557239621/100000000000000 : ℝ)^3417
        have hw : |(-48200131/250000000 : ℝ)|=(48200131/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2605980137/5000000000 : ℝ)|^4441 ≤ (535923180093/1250000000000 : ℝ)^3417
        have hw : |(2605980137/5000000000 : ℝ)|=(2605980137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721195199/5000000000 : ℝ)|^4441 ≤ (11338397084701/25000000000000 : ℝ)^3417
        have hw : |(2721195199/5000000000 : ℝ)|=(2721195199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s3_5 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294303567/10000000000 : ℝ)*x 0 + (-28372183/156250000 : ℝ)*x 1 + (5442390459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294303567/10000000000 : ℝ)^4441 ≤ (8751256199923/20000000000000 : ℝ)^3417 := by
    have hnat : (5294303567 : ℕ)^4441*20000000000000^3417 ≤ 8751256199923^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294303567 10000000000 8751256199923 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28372183/156250000 : ℝ)^4441 ≤ (10890129982371/100000000000000 : ℝ)^3417 := by
    have hnat : (28372183 : ℕ)^4441*100000000000000^3417 ≤ 10890129982371^3417*156250000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28372183 156250000 10890129982371 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442390459/10000000000 : ℝ)^4441 ≤ (45353588999479/100000000000000 : ℝ)^3417 := by
    have hnat : (5442390459 : ℕ)^4441*100000000000000^3417 ≤ 45353588999479^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442390459 10000000000 45353588999479 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294303567/10000000000 : ℝ), (-28372183/156250000 : ℝ), (5442390459/10000000000 : ℝ)] ![(8751256199923/20000000000000 : ℝ), (10890129982371/100000000000000 : ℝ), (45353588999479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294303567/10000000000 : ℝ)|^4441 ≤ (8751256199923/20000000000000 : ℝ)^3417
        have hw : |(5294303567/10000000000 : ℝ)|=(5294303567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28372183/156250000 : ℝ)|^4441 ≤ (10890129982371/100000000000000 : ℝ)^3417
        have hw : |(-28372183/156250000 : ℝ)|=(28372183/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442390459/10000000000 : ℝ)|^4441 ≤ (45353588999479/100000000000000 : ℝ)^3417
        have hw : |(5442390459/10000000000 : ℝ)|=(5442390459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s3_6 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294303653/10000000000 : ℝ)*x 0 + (1360597613/2500000000 : ℝ)*x 1 + (-453954901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294303653/10000000000 : ℝ)^4441 ≤ (43756281923389/100000000000000 : ℝ)^3417 := by
    have hnat : (5294303653 : ℕ)^4441*100000000000000^3417 ≤ 43756281923389^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294303653 10000000000 43756281923389 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360597613/2500000000 : ℝ)^4441 ≤ (2834599307729/6250000000000 : ℝ)^3417 := by
    have hnat : (1360597613 : ℕ)^4441*6250000000000^3417 ≤ 2834599307729^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360597613 2500000000 2834599307729 6250000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453954901/2500000000 : ℝ)^4441 ≤ (217802582811/2000000000000 : ℝ)^3417 := by
    have hnat : (453954901 : ℕ)^4441*2000000000000^3417 ≤ 217802582811^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453954901 2500000000 217802582811 2000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294303653/10000000000 : ℝ), (1360597613/2500000000 : ℝ), (-453954901/2500000000 : ℝ)] ![(43756281923389/100000000000000 : ℝ), (2834599307729/6250000000000 : ℝ), (217802582811/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294303653/10000000000 : ℝ)|^4441 ≤ (43756281923389/100000000000000 : ℝ)^3417
        have hw : |(5294303653/10000000000 : ℝ)|=(5294303653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360597613/2500000000 : ℝ)|^4441 ≤ (2834599307729/6250000000000 : ℝ)^3417
        have hw : |(1360597613/2500000000 : ℝ)|=(1360597613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-453954901/2500000000 : ℝ)|^4441 ≤ (217802582811/2000000000000 : ℝ)^3417
        have hw : |(-453954901/2500000000 : ℝ)|=(453954901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s3_7 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072088047/2500000000 : ℝ)*x 0 + (113723551/250000000 : ℝ)*x 1 + (1010278757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072088047/2500000000 : ℝ)^4441 ≤ (16636652917059/50000000000000 : ℝ)^3417 := by
    have hnat : (1072088047 : ℕ)^4441*50000000000000^3417 ≤ 16636652917059^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072088047 2500000000 16636652917059 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113723551/250000000 : ℝ)^4441 ≤ (17962370665023/50000000000000 : ℝ)^3417 := by
    have hnat : (113723551 : ℕ)^4441*50000000000000^3417 ≤ 17962370665023^3417*250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113723551 250000000 17962370665023 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010278757/2500000000 : ℝ)^4441 ≤ (30801952825369/100000000000000 : ℝ)^3417 := by
    have hnat : (1010278757 : ℕ)^4441*100000000000000^3417 ≤ 30801952825369^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010278757 2500000000 30801952825369 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072088047/2500000000 : ℝ), (113723551/250000000 : ℝ), (1010278757/2500000000 : ℝ)] ![(16636652917059/50000000000000 : ℝ), (17962370665023/50000000000000 : ℝ), (30801952825369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072088047/2500000000 : ℝ)|^4441 ≤ (16636652917059/50000000000000 : ℝ)^3417
        have hw : |(1072088047/2500000000 : ℝ)|=(1072088047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113723551/250000000 : ℝ)|^4441 ≤ (17962370665023/50000000000000 : ℝ)^3417
        have hw : |(113723551/250000000 : ℝ)|=(113723551/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010278757/2500000000 : ℝ)|^4441 ≤ (30801952825369/100000000000000 : ℝ)^3417
        have hw : |(1010278757/2500000000 : ℝ)|=(1010278757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1472_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2663/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15581/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10113/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10113/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10113/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10113/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10113/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10113/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10113/100000 : ℝ) ^ (4439/1024 : ℝ) ≤ (4855049959644951/100000000000000000000 : ℝ) := by
    have hpowers : (10113/100000 : ℝ)^4439 ≤ (4855049959644951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10113 : ℕ)^4439*100000000000000000000^1024 ≤ 4855049959644951^1024*100000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10113 100000 4855049959644951 100000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10113/100000 : ℝ)) (X := (4855049959644951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16169/100000 : ℝ) ^ (4439/1024 : ℝ) ≤ (7425101753142981/20000000000000000000 : ℝ) := by
    have hpowers : (16169/100000 : ℝ)^4439 ≤ (7425101753142981/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16169 : ℕ)^4439*20000000000000000000^1024 ≤ 7425101753142981^1024*100000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16169 100000 7425101753142981 20000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16169/100000 : ℝ)) (X := (7425101753142981/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004855049959644951/50000000000000000000 : ℝ) ≤ (10000223986730229/10000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (50004855049959644951/50000000000000000000 : ℝ)^1024 ≤ (10000223986730229/10000000000000000 : ℝ)^4439 := by
      have hnat : (50004855049959644951 : ℕ)^1024*10000000000000000^4439 ≤ 10000223986730229^4439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004855049959644951 50000000000000000000 10000223986730229 10000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000223986730229/10000000000000000 : ℝ)) (X := (50004855049959644951/50000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252623784920334991/6250000000000000000 : ℝ) ≤ (5000484131021123/5000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (6252623784920334991/6250000000000000000 : ℝ)^1024 ≤ (5000484131021123/5000000000000000 : ℝ)^4439 := by
      have hnat : (6252623784920334991 : ℕ)^1024*5000000000000000^4439 ≤ 5000484131021123^4439*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252623784920334991 6250000000000000000 5000484131021123 5000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000484131021123/5000000000000000 : ℝ)) (X := (6252623784920334991/6250000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007425101753142981/10000000000000000000 : ℝ) ≤ (10001712537354263/10000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (10007425101753142981/10000000000000000000 : ℝ)^1024 ≤ (10001712537354263/10000000000000000 : ℝ)^4439 := by
      have hnat : (10007425101753142981 : ℕ)^1024*10000000000000000^4439 ≤ 10001712537354263^4439*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007425101753142981 10000000000000000000 10001712537354263 10000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001712537354263/10000000000000000 : ℝ)) (X := (10007425101753142981/10000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4855049959644951/100000000000000000000 : ℝ) ≤ ((30273151375588705491/30280000000000000000 : ℝ)+2*(744275312017/605600000000000 : ℝ)*(10113/100000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (30273151375588705491/30280000000000000000 : ℝ)+2*(744275312017/605600000000000 : ℝ)*(10113/100000 : ℝ)=(10000223986730229/10000000000000000 : ℝ) by norm_num, show 1+2*(4855049959644951/100000000000000000000 : ℝ)=(50004855049959644951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7425101753142981/20000000000000000000 : ℝ)+(4855049959644951/100000000000000000000 : ℝ) ≤ ((30273151375588705491/30280000000000000000 : ℝ)+(744275312017/605600000000000 : ℝ)*((16169/100000 : ℝ)+(10113/100000 : ℝ)))^(4439/1024 : ℝ) := by
    rw [show (30273151375588705491/30280000000000000000 : ℝ)+(744275312017/605600000000000 : ℝ)*((16169/100000 : ℝ)+(10113/100000 : ℝ))=(5000484131021123/5000000000000000 : ℝ) by norm_num, show 1+(7425101753142981/20000000000000000000 : ℝ)+(4855049959644951/100000000000000000000 : ℝ)=(6252623784920334991/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7425101753142981/20000000000000000000 : ℝ) ≤ ((30273151375588705491/30280000000000000000 : ℝ)+2*(744275312017/605600000000000 : ℝ)*(16169/100000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (30273151375588705491/30280000000000000000 : ℝ)+2*(744275312017/605600000000000 : ℝ)*(16169/100000 : ℝ)=(10001712537354263/10000000000000000 : ℝ) by norm_num, show 1+2*(7425101753142981/20000000000000000000 : ℝ)=(10007425101753142981/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30273151375588705491/30280000000000000000 : ℝ)*(X 1 0+X 2 0)+(744275312017/605600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (10113/100000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (30273151375588705491/30280000000000000000 : ℝ)) (alpha := (744275312017/605600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30273151375588705491/30280000000000000000 : ℝ)*(X 0 1+X 2 1)+(744275312017/605600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (10113/100000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (30273151375588705491/30280000000000000000 : ℝ)) (alpha := (744275312017/605600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30273151375588705491/30280000000000000000 : ℝ)*(X 0 2+X 1 2)+(744275312017/605600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (10113/100000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (30273151375588705491/30280000000000000000 : ℝ)) (alpha := (744275312017/605600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2409963/12500000 : ℝ)*X 0 0+(680455183/1250000000 : ℝ)*X 0 1+(1042143731/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535505333/1000000000 : ℝ)*X 1 0+(-1023745741/5000000000 : ℝ)*X 1 1+(65133981/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355053387/10000000000 : ℝ)*X 2 0+(5210718491/10000000000 : ℝ)*X 2 1+(-204749139/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1072068797/2500000000 : ℝ)*X 0 0+(25239739/62500000 : ℝ)*X 0 1+(4551677879/10000000000 : ℝ)*X 0 2+(1072068797/2500000000 : ℝ)*X 1 0+(25239739/62500000 : ℝ)*X 1 1+(4551677879/10000000000 : ℝ)*X 1 2+(1072068797/2500000000 : ℝ)*X 2 0+(25239739/62500000 : ℝ)*X 2 1+(4551677879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-48200131/250000000 : ℝ)*X 0 0+(2605980137/5000000000 : ℝ)*X 0 1+(2721195199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294303567/10000000000 : ℝ)*X 1 0+(-28372183/156250000 : ℝ)*X 1 1+(5442390459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294303653/10000000000 : ℝ)*X 2 0+(1360597613/2500000000 : ℝ)*X 2 1+(-453954901/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1072088047/2500000000 : ℝ)*X 0 0+(113723551/250000000 : ℝ)*X 0 1+(1010278757/2500000000 : ℝ)*X 0 2+(1072088047/2500000000 : ℝ)*X 1 0+(113723551/250000000 : ℝ)*X 1 1+(1010278757/2500000000 : ℝ)*X 1 2+(1072088047/2500000000 : ℝ)*X 2 0+(113723551/250000000 : ℝ)*X 2 1+(1010278757/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63951108030732280404781179/6056000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2106578071/100000000000000 : ℝ)*(base19) + (1013555461/50000000000000 : ℝ)*(base23) + (67027041/100000000000000 : ℝ)*(lower2) + (108027557/50000000000000 : ℝ)*(upper3) + (212082619/100000000000000 : ℝ)*(upper5) + (24965833758123/800000000000 : ℝ)*(major0) + (24965833758123/800000000000 : ℝ)*(major1) + (24380697029417/781250000000 : ℝ)*(major2) + (67082768838017/1562500000000 : ℝ)*(sp0) + (2146663039357583/50000000000000 : ℝ)*(sp1) + (1073331539545579/25000000000000 : ℝ)*(sp2) + (974058286971351/50000000000000 : ℝ)*(sp3) + (619593203/2000000000000 : ℝ)*(sp4) + (13328296187/100000000000000 : ℝ)*(sp7) + (243516237779861/12500000000000 : ℝ)*(f.failure) + (2146664092646619/50000000000000 : ℝ)*(f.sum) + (13565753212847/60560000000000000000000000000 : ℝ)*base65 + (228028119870497807/24224000000000000000000000000000 : ℝ)*base68 + (1380435195037523149/189250000000000000000000000000000 : ℝ)*base70 + (195889655074977807/24224000000000000000000000000000 : ℝ)*base72 + (11970238483887/60560000000000000000000000000 : ℝ)*base73 + (1696321028867476851/189250000000000000000000000000000 : ℝ)*base75 + (371799289826472607/24224000000000000000000000000000 : ℝ)*base78 + (201736676733480607/24224000000000000000000000000000 : ℝ)*base80 + (3304812692749/6056000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5112197/1250000000000000000000 : ℝ)*base90 + (5112197/1250000000000000000000 : ℝ)*base92 + (17612197/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1950303058140808278527447241/189250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1461115213/100000000000000 : ℝ)*(base19) + (1813466919/100000000000000 : ℝ)*(base23) + (8906171/4000000000000 : ℝ)*(upper3) + (13561639/12500000000000 : ℝ)*(lower4) + (31830941/20000000000000 : ℝ)*(upper5) + (788610342111417/25000000000000 : ℝ)*(major0) + (788610342111417/25000000000000 : ℝ)*(major1) + (788610342111417/25000000000000 : ℝ)*(major2) + (20275961179/100000000000000 : ℝ)*(sp1) + (26980709359/100000000000000 : ℝ)*(sp2) + (4339707523667983/100000000000000 : ℝ)*(sp4) + (4339685786591591/100000000000000 : ℝ)*(sp5) + (542459841186463/12500000000000 : ℝ)*(sp6) + (98458743485447/5000000000000 : ℝ)*(sp7) + (98458743485447/5000000000000 : ℝ)*(f.failure) + (4339707523667983/100000000000000 : ℝ)*(f.sum) + (23234175587911/7570000000000000000000000000 : ℝ)*base66 + (2590020616467859253/757000000000000000000000000000000 : ℝ)*base68 + (6258618703751859253/757000000000000000000000000000000 : ℝ)*base70 + (6137547403832859253/757000000000000000000000000000000 : ℝ)*base72 + (5107725274011/7570000000000000000000000000 : ℝ)*base74 + (10863756686859253/757000000000000000000000000000000 : ℝ)*base76 + (337233599678859253/757000000000000000000000000000000 : ℝ)*base78 + (635435161337140747/757000000000000000000000000000000 : ℝ)*base79 + (16939995333491/7570000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (542281/500000000000000000000 : ℝ)*base89 + (542281/500000000000000000000 : ℝ)*base91 + (542281/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1472_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2663/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15581/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1472_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1472_s4_0 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-482164917/2500000000 : ℝ)*x 0 + (1087840359/2000000000 : ℝ)*x 1 + (1303676047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482164917/2500000000 : ℝ)^4441 ≤ (5888875502659/50000000000000 : ℝ)^3417 := by
    have hnat : (482164917 : ℕ)^4441*50000000000000^3417 ≤ 5888875502659^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482164917 2500000000 5888875502659 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087840359/2000000000 : ℝ)^4441 ≤ (9063811294131/20000000000000 : ℝ)^3417 := by
    have hnat : (1087840359 : ℕ)^4441*20000000000000^3417 ≤ 9063811294131^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087840359 2000000000 9063811294131 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303676047/2500000000 : ℝ)^4441 ≤ (42903192506841/100000000000000 : ℝ)^3417 := by
    have hnat : (1303676047 : ℕ)^4441*100000000000000^3417 ≤ 42903192506841^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303676047 2500000000 42903192506841 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-482164917/2500000000 : ℝ), (1087840359/2000000000 : ℝ), (1303676047/2500000000 : ℝ)] ![(5888875502659/50000000000000 : ℝ), (9063811294131/20000000000000 : ℝ), (42903192506841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-482164917/2500000000 : ℝ)|^4441 ≤ (5888875502659/50000000000000 : ℝ)^3417
        have hw : |(-482164917/2500000000 : ℝ)|=(482164917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087840359/2000000000 : ℝ)|^4441 ≤ (9063811294131/20000000000000 : ℝ)^3417
        have hw : |(1087840359/2000000000 : ℝ)|=(1087840359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303676047/2500000000 : ℝ)|^4441 ≤ (42903192506841/100000000000000 : ℝ)^3417
        have hw : |(1303676047/2500000000 : ℝ)|=(1303676047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s4_1 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676951453/5000000000 : ℝ)*x 0 + (-1021875371/5000000000 : ℝ)*x 1 + (5214704481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676951453/5000000000 : ℝ)^4441 ≤ (44397547906981/100000000000000 : ℝ)^3417 := by
    have hnat : (2676951453 : ℕ)^4441*100000000000000^3417 ≤ 44397547906981^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676951453 5000000000 44397547906981 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021875371/5000000000 : ℝ)^4441 ≤ (12699256433269/100000000000000 : ℝ)^3417 := by
    have hnat : (1021875371 : ℕ)^4441*100000000000000^3417 ≤ 12699256433269^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021875371 5000000000 12699256433269 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214704481/10000000000 : ℝ)^4441 ≤ (21451597819931/50000000000000 : ℝ)^3417 := by
    have hnat : (5214704481 : ℕ)^4441*50000000000000^3417 ≤ 21451597819931^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214704481 10000000000 21451597819931 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676951453/5000000000 : ℝ), (-1021875371/5000000000 : ℝ), (5214704481/10000000000 : ℝ)] ![(44397547906981/100000000000000 : ℝ), (12699256433269/100000000000000 : ℝ), (21451597819931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676951453/5000000000 : ℝ)|^4441 ≤ (44397547906981/100000000000000 : ℝ)^3417
        have hw : |(2676951453/5000000000 : ℝ)|=(2676951453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021875371/5000000000 : ℝ)|^4441 ≤ (12699256433269/100000000000000 : ℝ)^3417
        have hw : |(-1021875371/5000000000 : ℝ)|=(1021875371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214704481/10000000000 : ℝ)|^4441 ≤ (21451597819931/50000000000000 : ℝ)^3417
        have hw : |(5214704481/10000000000 : ℝ)|=(5214704481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s4_2 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676951527/5000000000 : ℝ)*x 0 + (5214704223/10000000000 : ℝ)*x 1 + (-2043750887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676951527/5000000000 : ℝ)^4441 ≤ (22198774751037/50000000000000 : ℝ)^3417 := by
    have hnat : (2676951527 : ℕ)^4441*50000000000000^3417 ≤ 22198774751037^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676951527 5000000000 22198774751037 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214704223/10000000000 : ℝ)^4441 ≤ (10725798220273/25000000000000 : ℝ)^3417 := by
    have hnat : (5214704223 : ℕ)^4441*25000000000000^3417 ≤ 10725798220273^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214704223 10000000000 10725798220273 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043750887/10000000000 : ℝ)^4441 ≤ (6349628802131/50000000000000 : ℝ)^3417 := by
    have hnat : (2043750887 : ℕ)^4441*50000000000000^3417 ≤ 6349628802131^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043750887 10000000000 6349628802131 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676951527/5000000000 : ℝ), (5214704223/10000000000 : ℝ), (-2043750887/10000000000 : ℝ)] ![(22198774751037/50000000000000 : ℝ), (10725798220273/25000000000000 : ℝ), (6349628802131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676951527/5000000000 : ℝ)|^4441 ≤ (22198774751037/50000000000000 : ℝ)^3417
        have hw : |(2676951527/5000000000 : ℝ)|=(2676951527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214704223/10000000000 : ℝ)|^4441 ≤ (10725798220273/25000000000000 : ℝ)^3417
        have hw : |(5214704223/10000000000 : ℝ)|=(5214704223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2043750887/10000000000 : ℝ)|^4441 ≤ (6349628802131/50000000000000 : ℝ)^3417
        have hw : |(-2043750887/10000000000 : ℝ)|=(2043750887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s4_3 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144351717/5000000000 : ℝ)*x 0 + (4047591469/10000000000 : ℝ)*x 1 + (4542343287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144351717/5000000000 : ℝ)^4441 ≤ (16638423955641/50000000000000 : ℝ)^3417 := by
    have hnat : (2144351717 : ℕ)^4441*50000000000000^3417 ≤ 16638423955641^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144351717 5000000000 16638423955641 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4047591469/10000000000 : ℝ)^4441 ≤ (3086612599429/10000000000000 : ℝ)^3417 := by
    have hnat : (4047591469 : ℕ)^4441*10000000000000^3417 ≤ 3086612599429^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047591469 10000000000 3086612599429 10000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542343287/10000000000 : ℝ)^4441 ≤ (17928513041017/50000000000000 : ℝ)^3417 := by
    have hnat : (4542343287 : ℕ)^4441*50000000000000^3417 ≤ 17928513041017^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542343287 10000000000 17928513041017 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144351717/5000000000 : ℝ), (4047591469/10000000000 : ℝ), (4542343287/10000000000 : ℝ)] ![(16638423955641/50000000000000 : ℝ), (3086612599429/10000000000000 : ℝ), (17928513041017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144351717/5000000000 : ℝ)|^4441 ≤ (16638423955641/50000000000000 : ℝ)^3417
        have hw : |(2144351717/5000000000 : ℝ)|=(2144351717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4047591469/10000000000 : ℝ)|^4441 ≤ (3086612599429/10000000000000 : ℝ)^3417
        have hw : |(4047591469/10000000000 : ℝ)|=(4047591469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4542343287/10000000000 : ℝ)|^4441 ≤ (17928513041017/50000000000000 : ℝ)^3417
        have hw : |(4542343287/10000000000 : ℝ)|=(4542343287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s4_4 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1928690873/10000000000 : ℝ)*x 0 + (651982237/1250000000 : ℝ)*x 1 + (2719019811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928690873/10000000000 : ℝ)^4441 ≤ (94223989377/800000000000 : ℝ)^3417 := by
    have hnat : (1928690873 : ℕ)^4441*800000000000^3417 ≤ 94223989377^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928690873 10000000000 94223989377 800000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651982237/1250000000 : ℝ)^4441 ≤ (42915529406351/100000000000000 : ℝ)^3417 := by
    have hnat : (651982237 : ℕ)^4441*100000000000000^3417 ≤ 42915529406351^3417*1250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651982237 1250000000 42915529406351 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719019811/5000000000 : ℝ)^4441 ≤ (22653235950647/50000000000000 : ℝ)^3417 := by
    have hnat : (2719019811 : ℕ)^4441*50000000000000^3417 ≤ 22653235950647^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719019811 5000000000 22653235950647 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1928690873/10000000000 : ℝ), (651982237/1250000000 : ℝ), (2719019811/5000000000 : ℝ)] ![(94223989377/800000000000 : ℝ), (42915529406351/100000000000000 : ℝ), (22653235950647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1928690873/10000000000 : ℝ)|^4441 ≤ (94223989377/800000000000 : ℝ)^3417
        have hw : |(-1928690873/10000000000 : ℝ)|=(1928690873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651982237/1250000000 : ℝ)|^4441 ≤ (42915529406351/100000000000000 : ℝ)^3417
        have hw : |(651982237/1250000000 : ℝ)|=(651982237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719019811/5000000000 : ℝ)|^4441 ≤ (22653235950647/50000000000000 : ℝ)^3417
        have hw : |(2719019811/5000000000 : ℝ)|=(2719019811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s4_5 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323838441/2500000000 : ℝ)*x 0 + (-910207797/5000000000 : ℝ)*x 1 + (5438039547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323838441/2500000000 : ℝ)^4441 ≤ (43767562088953/100000000000000 : ℝ)^3417 := by
    have hnat : (1323838441 : ℕ)^4441*100000000000000^3417 ≤ 43767562088953^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323838441 2500000000 43767562088953 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910207797/5000000000 : ℝ)^4441 ≤ (2185193362319/20000000000000 : ℝ)^3417 := by
    have hnat : (910207797 : ℕ)^4441*20000000000000^3417 ≤ 2185193362319^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910207797 5000000000 2185193362319 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438039547/10000000000 : ℝ)^4441 ≤ (1415827221537/3125000000000 : ℝ)^3417 := by
    have hnat : (5438039547 : ℕ)^4441*3125000000000^3417 ≤ 1415827221537^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438039547 10000000000 1415827221537 3125000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323838441/2500000000 : ℝ), (-910207797/5000000000 : ℝ), (5438039547/10000000000 : ℝ)] ![(43767562088953/100000000000000 : ℝ), (2185193362319/20000000000000 : ℝ), (1415827221537/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323838441/2500000000 : ℝ)|^4441 ≤ (43767562088953/100000000000000 : ℝ)^3417
        have hw : |(1323838441/2500000000 : ℝ)|=(1323838441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910207797/5000000000 : ℝ)|^4441 ≤ (2185193362319/20000000000000 : ℝ)^3417
        have hw : |(-910207797/5000000000 : ℝ)|=(910207797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438039547/10000000000 : ℝ)|^4441 ≤ (1415827221537/3125000000000 : ℝ)^3417
        have hw : |(5438039547/10000000000 : ℝ)|=(5438039547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s4_6 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295353689/10000000000 : ℝ)*x 0 + (5438039569/10000000000 : ℝ)*x 1 + (-910207833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295353689/10000000000 : ℝ)^4441 ≤ (5470945160411/12500000000000 : ℝ)^3417 := by
    have hnat : (5295353689 : ℕ)^4441*12500000000000^3417 ≤ 5470945160411^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295353689 10000000000 5470945160411 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438039569/10000000000 : ℝ)^4441 ≤ (22653235663701/50000000000000 : ℝ)^3417 := by
    have hnat : (5438039569 : ℕ)^4441*50000000000000^3417 ≤ 22653235663701^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438039569 10000000000 22653235663701 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910207833/5000000000 : ℝ)^4441 ≤ (2185193474647/20000000000000 : ℝ)^3417 := by
    have hnat : (910207833 : ℕ)^4441*20000000000000^3417 ≤ 2185193474647^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910207833 5000000000 2185193474647 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295353689/10000000000 : ℝ), (5438039569/10000000000 : ℝ), (-910207833/5000000000 : ℝ)] ![(5470945160411/12500000000000 : ℝ), (22653235663701/50000000000000 : ℝ), (2185193474647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295353689/10000000000 : ℝ)|^4441 ≤ (5470945160411/12500000000000 : ℝ)^3417
        have hw : |(5295353689/10000000000 : ℝ)|=(5295353689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438039569/10000000000 : ℝ)|^4441 ≤ (22653235663701/50000000000000 : ℝ)^3417
        have hw : |(5438039569/10000000000 : ℝ)|=(5438039569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-910207833/5000000000 : ℝ)|^4441 ≤ (2185193474647/20000000000000 : ℝ)^3417
        have hw : |(-910207833/5000000000 : ℝ)|=(910207833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s4_7 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144386017/5000000000 : ℝ)*x 0 + (1134950293/2500000000 : ℝ)*x 1 + (4050152709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144386017/5000000000 : ℝ)^4441 ≤ (16638769852901/50000000000000 : ℝ)^3417 := by
    have hnat : (2144386017 : ℕ)^4441*50000000000000^3417 ≤ 16638769852901^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144386017 5000000000 16638769852901 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134950293/2500000000 : ℝ)^4441 ≤ (2239434200349/6250000000000 : ℝ)^3417 := by
    have hnat : (1134950293 : ℕ)^4441*6250000000000^3417 ≤ 2239434200349^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134950293 2500000000 2239434200349 6250000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4050152709/10000000000 : ℝ)^4441 ≤ (6178302614169/20000000000000 : ℝ)^3417 := by
    have hnat : (4050152709 : ℕ)^4441*20000000000000^3417 ≤ 6178302614169^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4050152709 10000000000 6178302614169 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144386017/5000000000 : ℝ), (1134950293/2500000000 : ℝ), (4050152709/10000000000 : ℝ)] ![(16638769852901/50000000000000 : ℝ), (2239434200349/6250000000000 : ℝ), (6178302614169/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144386017/5000000000 : ℝ)|^4441 ≤ (16638769852901/50000000000000 : ℝ)^3417
        have hw : |(2144386017/5000000000 : ℝ)|=(2144386017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134950293/2500000000 : ℝ)|^4441 ≤ (2239434200349/6250000000000 : ℝ)^3417
        have hw : |(1134950293/2500000000 : ℝ)|=(1134950293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4050152709/10000000000 : ℝ)|^4441 ≤ (6178302614169/20000000000000 : ℝ)^3417
        have hw : |(4050152709/10000000000 : ℝ)|=(4050152709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1472_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2663/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5369/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15581/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2663/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15581/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2663/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15581/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2663/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15581/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2663/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15581/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2663/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15581/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2663/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2663/25000 : ℝ) ^ (4439/1024 : ℝ) ≤ (3040339376411263/50000000000000000000 : ℝ) := by
    have hpowers : (2663/25000 : ℝ)^4439 ≤ (3040339376411263/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2663 : ℕ)^4439*50000000000000000000^1024 ≤ 3040339376411263^1024*25000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2663 25000 3040339376411263 50000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2663/25000 : ℝ)) (X := (3040339376411263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15581/100000 : ℝ) ^ (4439/1024 : ℝ) ≤ (15808923161458279/50000000000000000000 : ℝ) := by
    have hpowers : (15581/100000 : ℝ)^4439 ≤ (15808923161458279/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15581 : ℕ)^4439*50000000000000000000^1024 ≤ 15808923161458279^1024*100000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15581 100000 15808923161458279 50000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15581/100000 : ℝ)) (X := (15808923161458279/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003040339376411263/25000000000000000000 : ℝ) ≤ (1250035066027171/1250000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (25003040339376411263/25000000000000000000 : ℝ)^1024 ≤ (1250035066027171/1250000000000000 : ℝ)^4439 := by
      have hnat : (25003040339376411263 : ℕ)^1024*1250000000000000^4439 ≤ 1250035066027171^4439*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003040339376411263 25000000000000000000 1250035066027171 1250000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035066027171/1250000000000000 : ℝ)) (X := (25003040339376411263/25000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009424631268934771/25000000000000000000 : ℝ) ≤ (10000869513246979/10000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (25009424631268934771/25000000000000000000 : ℝ)^1024 ≤ (10000869513246979/10000000000000000 : ℝ)^4439 := by
      have hnat : (25009424631268934771 : ℕ)^1024*10000000000000000^4439 ≤ 10000869513246979^4439*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009424631268934771 25000000000000000000 10000869513246979 10000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000869513246979/10000000000000000 : ℝ)) (X := (25009424631268934771/25000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015808923161458279/25000000000000000000 : ℝ) ≤ (1000145849827659/1000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (25015808923161458279/25000000000000000000 : ℝ)^1024 ≤ (1000145849827659/1000000000000000 : ℝ)^4439 := by
      have hnat : (25015808923161458279 : ℕ)^1024*1000000000000000^4439 ≤ 1000145849827659^4439*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015808923161458279 25000000000000000000 1000145849827659 1000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000145849827659/1000000000000000 : ℝ)) (X := (25015808923161458279/25000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3040339376411263/50000000000000000000 : ℝ) ≤ ((58111833710510111/58125000000000000 : ℝ)+2*(11112925087/9300000000000 : ℝ)*(2663/25000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (58111833710510111/58125000000000000 : ℝ)+2*(11112925087/9300000000000 : ℝ)*(2663/25000 : ℝ)=(1250035066027171/1250000000000000 : ℝ) by norm_num, show 1+2*(3040339376411263/50000000000000000000 : ℝ)=(25003040339376411263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15808923161458279/50000000000000000000 : ℝ)+(3040339376411263/50000000000000000000 : ℝ) ≤ ((58111833710510111/58125000000000000 : ℝ)+(11112925087/9300000000000 : ℝ)*((15581/100000 : ℝ)+(2663/25000 : ℝ)))^(4439/1024 : ℝ) := by
    rw [show (58111833710510111/58125000000000000 : ℝ)+(11112925087/9300000000000 : ℝ)*((15581/100000 : ℝ)+(2663/25000 : ℝ))=(10000869513246979/10000000000000000 : ℝ) by norm_num, show 1+(15808923161458279/50000000000000000000 : ℝ)+(3040339376411263/50000000000000000000 : ℝ)=(25009424631268934771/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15808923161458279/50000000000000000000 : ℝ) ≤ ((58111833710510111/58125000000000000 : ℝ)+2*(11112925087/9300000000000 : ℝ)*(15581/100000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (58111833710510111/58125000000000000 : ℝ)+2*(11112925087/9300000000000 : ℝ)*(15581/100000 : ℝ)=(1000145849827659/1000000000000000 : ℝ) by norm_num, show 1+2*(15808923161458279/50000000000000000000 : ℝ)=(25015808923161458279/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58111833710510111/58125000000000000 : ℝ)*(X 1 0+X 2 0)+(11112925087/9300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (2663/25000 : ℝ)) (hi := (15581/100000 : ℝ)) (c := (58111833710510111/58125000000000000 : ℝ)) (alpha := (11112925087/9300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58111833710510111/58125000000000000 : ℝ)*(X 0 1+X 2 1)+(11112925087/9300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (2663/25000 : ℝ)) (hi := (15581/100000 : ℝ)) (c := (58111833710510111/58125000000000000 : ℝ)) (alpha := (11112925087/9300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58111833710510111/58125000000000000 : ℝ)*(X 0 2+X 1 2)+(11112925087/9300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (2663/25000 : ℝ)) (hi := (15581/100000 : ℝ)) (c := (58111833710510111/58125000000000000 : ℝ)) (alpha := (11112925087/9300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-482164917/2500000000 : ℝ)*X 0 0+(1087840359/2000000000 : ℝ)*X 0 1+(1303676047/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676951453/5000000000 : ℝ)*X 1 0+(-1021875371/5000000000 : ℝ)*X 1 1+(5214704481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676951527/5000000000 : ℝ)*X 2 0+(5214704223/10000000000 : ℝ)*X 2 1+(-2043750887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2144351717/5000000000 : ℝ)*X 0 0+(4047591469/10000000000 : ℝ)*X 0 1+(4542343287/10000000000 : ℝ)*X 0 2+(2144351717/5000000000 : ℝ)*X 1 0+(4047591469/10000000000 : ℝ)*X 1 1+(4542343287/10000000000 : ℝ)*X 1 2+(2144351717/5000000000 : ℝ)*X 2 0+(4047591469/10000000000 : ℝ)*X 2 1+(4542343287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1928690873/10000000000 : ℝ)*X 0 0+(651982237/1250000000 : ℝ)*X 0 1+(2719019811/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323838441/2500000000 : ℝ)*X 1 0+(-910207797/5000000000 : ℝ)*X 1 1+(5438039547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295353689/10000000000 : ℝ)*X 2 0+(5438039569/10000000000 : ℝ)*X 2 1+(-910207833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2144386017/5000000000 : ℝ)*X 0 0+(1134950293/2500000000 : ℝ)*X 0 1+(4050152709/10000000000 : ℝ)*X 0 2+(2144386017/5000000000 : ℝ)*X 1 0+(1134950293/2500000000 : ℝ)*X 1 1+(4050152709/10000000000 : ℝ)*X 1 2+(2144386017/5000000000 : ℝ)*X 2 0+(1134950293/2500000000 : ℝ)*X 2 1+(4050152709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83707305223318245560237/19375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199861543/25000000000000 : ℝ)*(base19) + (164825169/20000000000000 : ℝ)*(base23) + (1054243/2000000000000 : ℝ)*(lower2) + (221484209/100000000000000 : ℝ)*(upper3) + (35454599/100000000000000 : ℝ)*(upper5) + (16189116909373/500000000000 : ℝ)*(major0) + (16189116909373/500000000000 : ℝ)*(major1) + (3237823381874601/100000000000000 : ℝ)*(major2) + (2227203539817049/50000000000000 : ℝ)*(sp0) + (556802417035677/12500000000000 : ℝ)*(sp1) + (278401206975359/6250000000000 : ℝ)*(sp2) + (1010609817381573/50000000000000 : ℝ)*(sp3) + (13056097491/100000000000000 : ℝ)*(sp4) + (1712310473/25000000000000 : ℝ)*(sp7) + (2021226484005037/100000000000000 : ℝ)*(f.failure) + (1113605033932897/25000000000000 : ℝ)*(f.sum) + (225029198563/930000000000000000000000000 : ℝ)*base66 + (125446484647513/116250000000000000000000000000 : ℝ)*base68 + (20589371760909289/5812500000000000000000000000000 : ℝ)*base70 + (940029630262513/116250000000000000000000000000 : ℝ)*base72 + (4025834704693/930000000000000000000000000 : ℝ)*base74 + (39807395794715711/5812500000000000000000000000000 : ℝ)*base75 + (13795493566801/9687500000000000000000000000 : ℝ)*base77 + (9871492249081/2421875000000000000000000000 : ℝ)*base80 + (24636858827/46500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (14182851/10000000000000000000000 : ℝ)*base89 + (14182851/10000000000000000000000 : ℝ)*base91 + (85817149/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2593736091948594664048971/484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (750855467/100000000000000 : ℝ)*(base19) + (17907413/2500000000000 : ℝ)*(base23) + (40550167/50000000000000 : ℝ)*(upper3) + (24853203/100000000000000 : ℝ)*(lower4) + (55051789/50000000000000 : ℝ)*(upper5) + (1635775296744193/50000000000000 : ℝ)*(major0) + (1635775296744193/50000000000000 : ℝ)*(major1) + (1635775296744193/50000000000000 : ℝ)*(major2) + (407783361/4000000000000 : ℝ)*(sp1) + (4294766689/50000000000000 : ℝ)*(sp2) + (562602519237611/12500000000000 : ℝ)*(sp4) + (900161841692279/20000000000000 : ℝ)*(sp5) + (450081084807099/10000000000000 : ℝ)*(sp6) + (2042280854582211/100000000000000 : ℝ)*(sp7) + (2042280854582211/100000000000000 : ℝ)*(f.failure) + (562602519237611/12500000000000 : ℝ)*(f.sum) + (60526486427/29062500000000000000000000 : ℝ)*base65 + (2397167632951391/968750000000000000000000000000 : ℝ)*base67 + (13262367080954859/968750000000000000000000000000 : ℝ)*base70 + (5665100854048609/968750000000000000000000000000 : ℝ)*base72 + (919087061251/232500000000000000000000000 : ℝ)*base73 + (6797239342642359/968750000000000000000000000000 : ℝ)*base76 + (10284973786923609/968750000000000000000000000000 : ℝ)*base78 + (6244902855673609/968750000000000000000000000000 : ℝ)*base80 + (314339892137/465000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (17691853/10000000000000000000000 : ℝ)*base89 + (17691853/10000000000000000000000 : ℝ)*base91 + (17691853/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1472_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2663/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1472_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1472_s5_0 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-385751213/2000000000 : ℝ)*x 0 + (5438572639/10000000000 : ℝ)*x 1 + (5215269771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385751213/2000000000 : ℝ)^4441 ≤ (5889258044849/50000000000000 : ℝ)^3417 := by
    have hnat : (385751213 : ℕ)^4441*50000000000000^3417 ≤ 5889258044849^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385751213 2000000000 5889258044849 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438572639/10000000000 : ℝ)^4441 ≤ (22656121783107/50000000000000 : ℝ)^3417 := by
    have hnat : (5438572639 : ℕ)^4441*50000000000000^3417 ≤ 22656121783107^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438572639 10000000000 22656121783107 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215269771/10000000000 : ℝ)^4441 ≤ (4290924033067/10000000000000 : ℝ)^3417 := by
    have hnat : (5215269771 : ℕ)^4441*10000000000000^3417 ≤ 4290924033067^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215269771 10000000000 4290924033067 10000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385751213/2000000000 : ℝ), (5438572639/10000000000 : ℝ), (5215269771/10000000000 : ℝ)] ![(5889258044849/50000000000000 : ℝ), (22656121783107/50000000000000 : ℝ), (4290924033067/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385751213/2000000000 : ℝ)|^4441 ≤ (5889258044849/50000000000000 : ℝ)^3417
        have hw : |(-385751213/2000000000 : ℝ)|=(385751213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438572639/10000000000 : ℝ)|^4441 ≤ (22656121783107/50000000000000 : ℝ)^3417
        have hw : |(5438572639/10000000000 : ℝ)|=(5438572639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215269771/10000000000 : ℝ)|^4441 ≤ (4290924033067/10000000000000 : ℝ)^3417
        have hw : |(5215269771/10000000000 : ℝ)|=(5215269771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s5_1 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353739949/10000000000 : ℝ)*x 0 + (-1021609917/5000000000 : ℝ)*x 1 + (651908709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353739949/10000000000 : ℝ)^4441 ≤ (22197895810311/50000000000000 : ℝ)^3417 := by
    have hnat : (5353739949 : ℕ)^4441*50000000000000^3417 ≤ 22197895810311^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353739949 10000000000 22197895810311 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021609917/5000000000 : ℝ)^4441 ≤ (1269496908737/10000000000000 : ℝ)^3417 := by
    have hnat : (1021609917 : ℕ)^4441*10000000000000^3417 ≤ 1269496908737^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021609917 5000000000 1269496908737 10000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651908709/1250000000 : ℝ)^4441 ≤ (21454619636019/50000000000000 : ℝ)^3417 := by
    have hnat : (651908709 : ℕ)^4441*50000000000000^3417 ≤ 21454619636019^3417*1250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651908709 1250000000 21454619636019 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353739949/10000000000 : ℝ), (-1021609917/5000000000 : ℝ), (651908709/1250000000 : ℝ)] ![(22197895810311/50000000000000 : ℝ), (1269496908737/10000000000000 : ℝ), (21454619636019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353739949/10000000000 : ℝ)|^4441 ≤ (22197895810311/50000000000000 : ℝ)^3417
        have hw : |(5353739949/10000000000 : ℝ)|=(5353739949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021609917/5000000000 : ℝ)|^4441 ≤ (1269496908737/10000000000000 : ℝ)^3417
        have hw : |(-1021609917/5000000000 : ℝ)|=(1021609917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651908709/1250000000 : ℝ)|^4441 ≤ (21454619636019/50000000000000 : ℝ)^3417
        have hw : |(651908709/1250000000 : ℝ)|=(651908709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s5_2 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353740209/10000000000 : ℝ)*x 0 + (1303817333/2500000000 : ℝ)*x 1 + (-2043219937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353740209/10000000000 : ℝ)^4441 ≤ (44395794422787/100000000000000 : ℝ)^3417 := by
    have hnat : (5353740209 : ℕ)^4441*100000000000000^3417 ≤ 44395794422787^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353740209 10000000000 44395794422787 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303817333/2500000000 : ℝ)^4441 ≤ (10727308909083/25000000000000 : ℝ)^3417 := by
    have hnat : (1303817333 : ℕ)^4441*25000000000000^3417 ≤ 10727308909083^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303817333 2500000000 10727308909083 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043219937/10000000000 : ℝ)^4441 ≤ (6347484959557/50000000000000 : ℝ)^3417 := by
    have hnat : (2043219937 : ℕ)^4441*50000000000000^3417 ≤ 6347484959557^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043219937 10000000000 6347484959557 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353740209/10000000000 : ℝ), (1303817333/2500000000 : ℝ), (-2043219937/10000000000 : ℝ)] ![(44395794422787/100000000000000 : ℝ), (10727308909083/25000000000000 : ℝ), (6347484959557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353740209/10000000000 : ℝ)|^4441 ≤ (44395794422787/100000000000000 : ℝ)^3417
        have hw : |(5353740209/10000000000 : ℝ)|=(5353740209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303817333/2500000000 : ℝ)|^4441 ≤ (10727308909083/25000000000000 : ℝ)^3417
        have hw : |(1303817333/2500000000 : ℝ)|=(1303817333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2043219937/10000000000 : ℝ)|^4441 ≤ (6347484959557/50000000000000 : ℝ)^3417
        have hw : |(-2043219937/10000000000 : ℝ)|=(2043219937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s5_3 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4288762527/10000000000 : ℝ)*x 0 + (202445039/500000000 : ℝ)*x 1 + (567627531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288762527/10000000000 : ℝ)^4441 ≤ (6655488766513/20000000000000 : ℝ)^3417 := by
    have hnat : (4288762527 : ℕ)^4441*20000000000000^3417 ≤ 6655488766513^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288762527 10000000000 6655488766513 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202445039/500000000 : ℝ)^4441 ≤ (30879103317217/100000000000000 : ℝ)^3417 := by
    have hnat : (202445039 : ℕ)^4441*100000000000000^3417 ≤ 30879103317217^3417*500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202445039 500000000 30879103317217 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567627531/1250000000 : ℝ)^4441 ≤ (1120107901049/3125000000000 : ℝ)^3417 := by
    have hnat : (567627531 : ℕ)^4441*3125000000000^3417 ≤ 1120107901049^3417*1250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567627531 1250000000 1120107901049 3125000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288762527/10000000000 : ℝ), (202445039/500000000 : ℝ), (567627531/1250000000 : ℝ)] ![(6655488766513/20000000000000 : ℝ), (30879103317217/100000000000000 : ℝ), (1120107901049/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288762527/10000000000 : ℝ)|^4441 ≤ (6655488766513/20000000000000 : ℝ)^3417
        have hw : |(4288762527/10000000000 : ℝ)|=(4288762527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(202445039/500000000 : ℝ)|^4441 ≤ (30879103317217/100000000000000 : ℝ)^3417
        have hw : |(202445039/500000000 : ℝ)|=(202445039/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567627531/1250000000 : ℝ)|^4441 ≤ (1120107901049/3125000000000 : ℝ)^3417
        have hw : |(567627531/1250000000 : ℝ)|=(567627531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s5_4 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1928786731/10000000000 : ℝ)*x 0 + (260820557/500000000 : ℝ)*x 1 + (543742297/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928786731/10000000000 : ℝ)^4441 ≤ (5889379741111/50000000000000 : ℝ)^3417 := by
    have hnat : (1928786731 : ℕ)^4441*50000000000000^3417 ≤ 5889379741111^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928786731 10000000000 5889379741111 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260820557/500000000 : ℝ)^4441 ≤ (42921445678357/100000000000000 : ℝ)^3417 := by
    have hnat : (260820557 : ℕ)^4441*100000000000000^3417 ≤ 42921445678357^3417*500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260820557 500000000 42921445678357 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543742297/1000000000 : ℝ)^4441 ≤ (45299794823503/100000000000000 : ℝ)^3417 := by
    have hnat : (543742297 : ℕ)^4441*100000000000000^3417 ≤ 45299794823503^3417*1000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543742297 1000000000 45299794823503 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1928786731/10000000000 : ℝ), (260820557/500000000 : ℝ), (543742297/1000000000 : ℝ)] ![(5889379741111/50000000000000 : ℝ), (42921445678357/100000000000000 : ℝ), (45299794823503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1928786731/10000000000 : ℝ)|^4441 ≤ (5889379741111/50000000000000 : ℝ)^3417
        have hw : |(-1928786731/10000000000 : ℝ)|=(1928786731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260820557/500000000 : ℝ)|^4441 ≤ (42921445678357/100000000000000 : ℝ)^3417
        have hw : |(260820557/500000000 : ℝ)|=(260820557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543742297/1000000000 : ℝ)|^4441 ≤ (45299794823503/100000000000000 : ℝ)^3417
        have hw : |(543742297/1000000000 : ℝ)|=(543742297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s5_5 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647751289/5000000000 : ℝ)*x 0 + (-455266649/2500000000 : ℝ)*x 1 + (2718711449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647751289/5000000000 : ℝ)^4441 ≤ (43769160685207/100000000000000 : ℝ)^3417 := by
    have hnat : (2647751289 : ℕ)^4441*100000000000000^3417 ≤ 43769160685207^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647751289 5000000000 43769160685207 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455266649/2500000000 : ℝ)^4441 ≤ (2732761314039/25000000000000 : ℝ)^3417 := by
    have hnat : (455266649 : ℕ)^4441*25000000000000^3417 ≤ 2732761314039^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455266649 2500000000 2732761314039 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718711449/5000000000 : ℝ)^4441 ≤ (44238080121/97656250000 : ℝ)^3417 := by
    have hnat : (2718711449 : ℕ)^4441*97656250000^3417 ≤ 44238080121^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718711449 5000000000 44238080121 97656250000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647751289/5000000000 : ℝ), (-455266649/2500000000 : ℝ), (2718711449/5000000000 : ℝ)] ![(43769160685207/100000000000000 : ℝ), (2732761314039/25000000000000 : ℝ), (44238080121/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647751289/5000000000 : ℝ)|^4441 ≤ (43769160685207/100000000000000 : ℝ)^3417
        have hw : |(2647751289/5000000000 : ℝ)|=(2647751289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-455266649/2500000000 : ℝ)|^4441 ≤ (2732761314039/25000000000000 : ℝ)^3417
        have hw : |(-455266649/2500000000 : ℝ)|=(455266649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718711449/5000000000 : ℝ)|^4441 ≤ (44238080121/97656250000 : ℝ)^3417
        have hw : |(2718711449/5000000000 : ℝ)|=(2718711449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s5_6 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295502567/10000000000 : ℝ)*x 0 + (2718711471/5000000000 : ℝ)*x 1 + (-1821066551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295502567/10000000000 : ℝ)^4441 ≤ (21884580283521/50000000000000 : ℝ)^3417 := by
    have hnat : (5295502567 : ℕ)^4441*50000000000000^3417 ≤ 21884580283521^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295502567 10000000000 21884580283521 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718711471/5000000000 : ℝ)^4441 ≤ (22649897260163/50000000000000 : ℝ)^3417 := by
    have hnat : (2718711471 : ℕ)^4441*50000000000000^3417 ≤ 22649897260163^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718711471 5000000000 22649897260163 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1821066551/10000000000 : ℝ)^4441 ≤ (5465522452547/50000000000000 : ℝ)^3417 := by
    have hnat : (1821066551 : ℕ)^4441*50000000000000^3417 ≤ 5465522452547^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821066551 10000000000 5465522452547 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295502567/10000000000 : ℝ), (2718711471/5000000000 : ℝ), (-1821066551/10000000000 : ℝ)] ![(21884580283521/50000000000000 : ℝ), (22649897260163/50000000000000 : ℝ), (5465522452547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295502567/10000000000 : ℝ)|^4441 ≤ (21884580283521/50000000000000 : ℝ)^3417
        have hw : |(5295502567/10000000000 : ℝ)|=(5295502567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718711471/5000000000 : ℝ)|^4441 ≤ (22649897260163/50000000000000 : ℝ)^3417
        have hw : |(2718711471/5000000000 : ℝ)|=(2718711471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1821066551/10000000000 : ℝ)|^4441 ≤ (5465522452547/50000000000000 : ℝ)^3417
        have hw : |(-1821066551/10000000000 : ℝ)|=(1821066551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s5_7 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4288830439/10000000000 : ℝ)*x 0 + (4538504897/10000000000 : ℝ)*x 1 + (506429319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288830439/10000000000 : ℝ)^4441 ≤ (33278128691781/100000000000000 : ℝ)^3417 := by
    have hnat : (4288830439 : ℕ)^4441*100000000000000^3417 ≤ 33278128691781^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288830439 10000000000 33278128691781 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538504897/10000000000 : ℝ)^4441 ≤ (35817650752257/100000000000000 : ℝ)^3417 := by
    have hnat : (4538504897 : ℕ)^4441*100000000000000^3417 ≤ 35817650752257^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538504897 10000000000 35817650752257 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506429319/1250000000 : ℝ)^4441 ≤ (30904220538303/100000000000000 : ℝ)^3417 := by
    have hnat : (506429319 : ℕ)^4441*100000000000000^3417 ≤ 30904220538303^3417*1250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506429319 1250000000 30904220538303 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288830439/10000000000 : ℝ), (4538504897/10000000000 : ℝ), (506429319/1250000000 : ℝ)] ![(33278128691781/100000000000000 : ℝ), (35817650752257/100000000000000 : ℝ), (30904220538303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288830439/10000000000 : ℝ)|^4441 ≤ (33278128691781/100000000000000 : ℝ)^3417
        have hw : |(4288830439/10000000000 : ℝ)|=(4288830439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538504897/10000000000 : ℝ)|^4441 ≤ (35817650752257/100000000000000 : ℝ)^3417
        have hw : |(4538504897/10000000000 : ℝ)|=(4538504897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(506429319/1250000000 : ℝ)|^4441 ≤ (30904220538303/100000000000000 : ℝ)^3417
        have hw : |(506429319/1250000000 : ℝ)|=(506429319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1472_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (43/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (619/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5369/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5369/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5369/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5369/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5369/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5369/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5369/50000 : ℝ) ^ (4439/1024 : ℝ) ≤ (1259275597524921/20000000000000000000 : ℝ) := by
    have hpowers : (5369/50000 : ℝ)^4439 ≤ (1259275597524921/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5369 : ℕ)^4439*20000000000000000000^1024 ≤ 1259275597524921^1024*50000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5369 50000 1259275597524921 20000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5369/50000 : ℝ)) (X := (1259275597524921/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4439/1024 : ℝ) ≤ (30807853437933817/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4439 ≤ (30807853437933817/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4439*100000000000000000000^1024 ≤ 30807853437933817^1024*3125^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 30807853437933817 100000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (30807853437933817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001259275597524921/10000000000000000000 : ℝ) ≤ (5000145239440677/5000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (10001259275597524921/10000000000000000000 : ℝ)^1024 ≤ (5000145239440677/5000000000000000 : ℝ)^4439 := by
      have hnat : (10001259275597524921 : ℕ)^1024*5000000000000000^4439 ≤ 5000145239440677^4439*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001259275597524921 10000000000000000000 5000145239440677 5000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000145239440677/5000000000000000 : ℝ)) (X := (10001259275597524921/10000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018552115712779211/50000000000000000000 : ℝ) ≤ (10000855807870713/10000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (50018552115712779211/50000000000000000000 : ℝ)^1024 ≤ (10000855807870713/10000000000000000 : ℝ)^4439 := by
      have hnat : (50018552115712779211 : ℕ)^1024*10000000000000000^4439 ≤ 10000855807870713^4439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018552115712779211 50000000000000000000 10000855807870713 10000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000855807870713/10000000000000000 : ℝ)) (X := (50018552115712779211/50000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030807853437933817/50000000000000000000 : ℝ) ≤ (1250177642107509/1250000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (50030807853437933817/50000000000000000000 : ℝ)^1024 ≤ (1250177642107509/1250000000000000 : ℝ)^4439 := by
      have hnat : (50030807853437933817 : ℕ)^1024*1250000000000000^4439 ≤ 1250177642107509^4439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030807853437933817 50000000000000000000 1250177642107509 1250000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250177642107509/1250000000000000 : ℝ)) (X := (50030807853437933817/50000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1259275597524921/20000000000000000000 : ℝ) ≤ ((2968077423081934851/2968750000000000000 : ℝ)+2*(565328989359/475000000000000 : ℝ)*(5369/50000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (2968077423081934851/2968750000000000000 : ℝ)+2*(565328989359/475000000000000 : ℝ)*(5369/50000 : ℝ)=(5000145239440677/5000000000000000 : ℝ) by norm_num, show 1+2*(1259275597524921/20000000000000000000 : ℝ)=(10001259275597524921/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30807853437933817/100000000000000000000 : ℝ)+(1259275597524921/20000000000000000000 : ℝ) ≤ ((2968077423081934851/2968750000000000000 : ℝ)+(565328989359/475000000000000 : ℝ)*((484/3125 : ℝ)+(5369/50000 : ℝ)))^(4439/1024 : ℝ) := by
    rw [show (2968077423081934851/2968750000000000000 : ℝ)+(565328989359/475000000000000 : ℝ)*((484/3125 : ℝ)+(5369/50000 : ℝ))=(10000855807870713/10000000000000000 : ℝ) by norm_num, show 1+(30807853437933817/100000000000000000000 : ℝ)+(1259275597524921/20000000000000000000 : ℝ)=(50018552115712779211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30807853437933817/100000000000000000000 : ℝ) ≤ ((2968077423081934851/2968750000000000000 : ℝ)+2*(565328989359/475000000000000 : ℝ)*(484/3125 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (2968077423081934851/2968750000000000000 : ℝ)+2*(565328989359/475000000000000 : ℝ)*(484/3125 : ℝ)=(1250177642107509/1250000000000000 : ℝ) by norm_num, show 1+2*(30807853437933817/100000000000000000000 : ℝ)=(50030807853437933817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2968077423081934851/2968750000000000000 : ℝ)*(X 1 0+X 2 0)+(565328989359/475000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2968077423081934851/2968750000000000000 : ℝ)) (alpha := (565328989359/475000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2968077423081934851/2968750000000000000 : ℝ)*(X 0 1+X 2 1)+(565328989359/475000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2968077423081934851/2968750000000000000 : ℝ)) (alpha := (565328989359/475000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2968077423081934851/2968750000000000000 : ℝ)*(X 0 2+X 1 2)+(565328989359/475000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2968077423081934851/2968750000000000000 : ℝ)) (alpha := (565328989359/475000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-385751213/2000000000 : ℝ)*X 0 0+(5438572639/10000000000 : ℝ)*X 0 1+(5215269771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353739949/10000000000 : ℝ)*X 1 0+(-1021609917/5000000000 : ℝ)*X 1 1+(651908709/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353740209/10000000000 : ℝ)*X 2 0+(1303817333/2500000000 : ℝ)*X 2 1+(-2043219937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4288762527/10000000000 : ℝ)*X 0 0+(202445039/500000000 : ℝ)*X 0 1+(567627531/1250000000 : ℝ)*X 0 2+(4288762527/10000000000 : ℝ)*X 1 0+(202445039/500000000 : ℝ)*X 1 1+(567627531/1250000000 : ℝ)*X 1 2+(4288762527/10000000000 : ℝ)*X 2 0+(202445039/500000000 : ℝ)*X 2 1+(567627531/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1928786731/10000000000 : ℝ)*X 0 0+(260820557/500000000 : ℝ)*X 0 1+(543742297/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647751289/5000000000 : ℝ)*X 1 0+(-455266649/2500000000 : ℝ)*X 1 1+(2718711449/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295502567/10000000000 : ℝ)*X 2 0+(2718711471/5000000000 : ℝ)*X 2 1+(-1821066551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4288830439/10000000000 : ℝ)*X 0 0+(4538504897/10000000000 : ℝ)*X 0 1+(506429319/1250000000 : ℝ)*X 0 2+(4288830439/10000000000 : ℝ)*X 1 0+(4538504897/10000000000 : ℝ)*X 1 1+(506429319/1250000000 : ℝ)*X 1 2+(4288830439/10000000000 : ℝ)*X 2 0+(4538504897/10000000000 : ℝ)*X 2 1+(506429319/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87687912849446305822227873/18554687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (11058089/1000000000000 : ℝ)*(base19) + (1250021581/100000000000000 : ℝ)*(base23) + (177150611/100000000000000 : ℝ)*(upper3) + (39226791/100000000000000 : ℝ)*(upper4) + (13221833/20000000000000 : ℝ)*(upper5) + (813786497600919/25000000000000 : ℝ)*(major0) + (813786497600919/25000000000000 : ℝ)*(major1) + (813786497600919/25000000000000 : ℝ)*(major2) + (1119559443105771/25000000000000 : ℝ)*(sp0) + (4478250513564767/100000000000000 : ℝ)*(sp1) + (2239125184676043/50000000000000 : ℝ)*(sp2) + (1016016278427151/50000000000000 : ℝ)*(sp3) + (1730868823/12500000000000 : ℝ)*(sp4) + (955881101/12500000000000 : ℝ)*(sp7) + (2032040203903109/100000000000000 : ℝ)*(f.failure) + (4478251619373667/100000000000000 : ℝ)*(f.sum) + (5862345733/11596679687500000000000000 : ℝ)*base65 + (1388755798260390681/74218750000000000000000000000000 : ℝ)*base68 + (1232611154885390681/74218750000000000000000000000000 : ℝ)*base70 + (964767234053359431/74218750000000000000000000000000 : ℝ)*base72 + (7404531049227/2968750000000000000000000000 : ℝ)*base74 + (240940160432265681/74218750000000000000000000000000 : ℝ)*base76 + (564687283776015681/74218750000000000000000000000000 : ℝ)*base78 + (798310174057265681/74218750000000000000000000000000 : ℝ)*base80 + (6809601481727/2968750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (23590507/10000000000000000000000 : ℝ)*base89 + (23590507/10000000000000000000000 : ℝ)*base91 + (23590507/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7308534019062097822317/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1057864853/100000000000000 : ℝ)*(base19) + (566890231/50000000000000 : ℝ)*(base23) + (119845713/100000000000000 : ℝ)*(upper3) + (8732027/25000000000000 : ℝ)*(lower4) + (25574239/20000000000000 : ℝ)*(upper5) + (3288867900043951/100000000000000 : ℝ)*(major0) + (3288867900043951/100000000000000 : ℝ)*(major1) + (3288867900043951/100000000000000 : ℝ)*(major2) + (118921827/800000000000 : ℝ)*(sp1) + (3325042277/20000000000000 : ℝ)*(sp2) + (565580542561911/12500000000000 : ℝ)*(sp4) + (4524628417402059/100000000000000 : ℝ)*(sp5) + (4524626581503441/100000000000000 : ℝ)*(sp6) + (1026545632349183/50000000000000 : ℝ)*(sp7) + (1026545632349183/50000000000000 : ℝ)*(f.failure) + (565580542561911/12500000000000 : ℝ)*(f.sum) + (808318073689/1250000000000000000000000000 : ℝ)*base66 + (20690765097168029/15625000000000000000000000000000 : ℝ)*base67 + (27863934434081971/15625000000000000000000000000000 : ℝ)*base70 + (34497000980956971/15625000000000000000000000000000 : ℝ)*base72 + (390621623811/1250000000000000000000000000 : ℝ)*base73 + (149912243347168029/15625000000000000000000000000000 : ℝ)*base75 + (31267818784668029/15625000000000000000000000000000 : ℝ)*base77 + (193565171184081971/15625000000000000000000000000000 : ℝ)*base80 + (3303534238811/1250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (32015791/5000000000000000000000 : ℝ)*base90 + (32015791/5000000000000000000000 : ℝ)*base92 + (32015791/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1472_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1472_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1472_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1472_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1472_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1472_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1472_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
