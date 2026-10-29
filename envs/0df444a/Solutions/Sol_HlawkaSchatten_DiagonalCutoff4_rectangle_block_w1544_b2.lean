-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1544_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:42.775999+00:00
-- url     : https://prove2.me/submissions/f6e9c871-2a2d-4556-8bb6-3ec70c70d95a

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
theorem support_rectangle_w1544_s6_0 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-72870381/400000000 : ℝ)*x 0 + (271454969/500000000 : ℝ)*x 1 + (5219096443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72870381/400000000 : ℝ)^4585 ≤ (11164469608037/100000000000000 : ℝ)^3561 := by
    have hnat : (72870381 : ℕ)^4585*100000000000000^3561 ≤ 11164469608037^3561*400000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72870381 400000000 11164469608037 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271454969/500000000 : ℝ)^4585 ≤ (22772788148433/50000000000000 : ℝ)^3561 := by
    have hnat : (271454969 : ℕ)^4585*50000000000000^3561 ≤ 22772788148433^3561*500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271454969 500000000 22772788148433 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219096443/10000000000 : ℝ)^4585 ≤ (4328995407127/10000000000000 : ℝ)^3561 := by
    have hnat : (5219096443 : ℕ)^4585*10000000000000^3561 ≤ 4328995407127^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219096443 10000000000 4328995407127 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72870381/400000000 : ℝ), (271454969/500000000 : ℝ), (5219096443/10000000000 : ℝ)] ![(11164469608037/100000000000000 : ℝ), (22772788148433/50000000000000 : ℝ), (4328995407127/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72870381/400000000 : ℝ)|^4585 ≤ (11164469608037/100000000000000 : ℝ)^3561
        have hw : |(-72870381/400000000 : ℝ)|=(72870381/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271454969/500000000 : ℝ)|^4585 ≤ (22772788148433/50000000000000 : ℝ)^3561
        have hw : |(271454969/500000000 : ℝ)|=(271454969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219096443/10000000000 : ℝ)|^4585 ≤ (4328995407127/10000000000000 : ℝ)^3561
        have hw : |(5219096443/10000000000 : ℝ)|=(5219096443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s6_1 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349754803/10000000000 : ℝ)*x 0 + (-1929245397/10000000000 : ℝ)*x 1 + (5219096771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349754803/10000000000 : ℝ)^4585 ≤ (1396573114819/3125000000000 : ℝ)^3561 := by
    have hnat : (5349754803 : ℕ)^4585*3125000000000^3561 ≤ 1396573114819^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349754803 10000000000 1396573114819 3125000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929245397/10000000000 : ℝ)^4585 ≤ (1201970273853/10000000000000 : ℝ)^3561 := by
    have hnat : (1929245397 : ℕ)^4585*10000000000000^3561 ≤ 1201970273853^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929245397 10000000000 1201970273853 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219096771/10000000000 : ℝ)^4585 ≤ (43289957574213/100000000000000 : ℝ)^3561 := by
    have hnat : (5219096771 : ℕ)^4585*100000000000000^3561 ≤ 43289957574213^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219096771 10000000000 43289957574213 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349754803/10000000000 : ℝ), (-1929245397/10000000000 : ℝ), (5219096771/10000000000 : ℝ)] ![(1396573114819/3125000000000 : ℝ), (1201970273853/10000000000000 : ℝ), (43289957574213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349754803/10000000000 : ℝ)|^4585 ≤ (1396573114819/3125000000000 : ℝ)^3561
        have hw : |(5349754803/10000000000 : ℝ)|=(5349754803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929245397/10000000000 : ℝ)|^4585 ≤ (1201970273853/10000000000000 : ℝ)^3561
        have hw : |(-1929245397/10000000000 : ℝ)|=(1929245397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219096771/10000000000 : ℝ)|^4585 ≤ (43289957574213/100000000000000 : ℝ)^3561
        have hw : |(5219096771/10000000000 : ℝ)|=(5219096771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s6_2 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337438747/2500000000 : ℝ)*x 0 + (5219096553/10000000000 : ℝ)*x 1 + (-964622719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337438747/2500000000 : ℝ)^4585 ≤ (44690341664051/100000000000000 : ℝ)^3561 := by
    have hnat : (1337438747 : ℕ)^4585*100000000000000^3561 ≤ 44690341664051^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337438747 2500000000 44690341664051 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219096553/10000000000 : ℝ)^4585 ≤ (21644977623019/50000000000000 : ℝ)^3561 := by
    have hnat : (5219096553 : ℕ)^4585*50000000000000^3561 ≤ 21644977623019^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219096553 10000000000 21644977623019 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964622719/5000000000 : ℝ)^4585 ≤ (480788122697/4000000000000 : ℝ)^3561 := by
    have hnat : (964622719 : ℕ)^4585*4000000000000^3561 ≤ 480788122697^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964622719 5000000000 480788122697 4000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337438747/2500000000 : ℝ), (5219096553/10000000000 : ℝ), (-964622719/5000000000 : ℝ)] ![(44690341664051/100000000000000 : ℝ), (21644977623019/50000000000000 : ℝ), (480788122697/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337438747/2500000000 : ℝ)|^4585 ≤ (44690341664051/100000000000000 : ℝ)^3561
        have hw : |(1337438747/2500000000 : ℝ)|=(1337438747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219096553/10000000000 : ℝ)|^4585 ≤ (21644977623019/50000000000000 : ℝ)^3561
        have hw : |(5219096553/10000000000 : ℝ)|=(5219096553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964622719/5000000000 : ℝ)|^4585 ≤ (480788122697/4000000000000 : ℝ)^3561
        have hw : |(-964622719/5000000000 : ℝ)|=(964622719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s6_3 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4255099813/10000000000 : ℝ)*x 0 + (2008690813/5000000000 : ℝ)*x 1 + (2252169067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255099813/10000000000 : ℝ)^4585 ≤ (33281214104029/100000000000000 : ℝ)^3561 := by
    have hnat : (4255099813 : ℕ)^4585*100000000000000^3561 ≤ 33281214104029^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255099813 10000000000 33281214104029 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008690813/5000000000 : ℝ)^4585 ≤ (3090673244987/10000000000000 : ℝ)^3561 := by
    have hnat : (2008690813 : ℕ)^4585*10000000000000^3561 ≤ 3090673244987^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008690813 5000000000 3090673244987 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252169067/5000000000 : ℝ)^4585 ≤ (35812053429423/100000000000000 : ℝ)^3561 := by
    have hnat : (2252169067 : ℕ)^4585*100000000000000^3561 ≤ 35812053429423^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252169067 5000000000 35812053429423 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255099813/10000000000 : ℝ), (2008690813/5000000000 : ℝ), (2252169067/5000000000 : ℝ)] ![(33281214104029/100000000000000 : ℝ), (3090673244987/10000000000000 : ℝ), (35812053429423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255099813/10000000000 : ℝ)|^4585 ≤ (33281214104029/100000000000000 : ℝ)^3561
        have hw : |(4255099813/10000000000 : ℝ)|=(4255099813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008690813/5000000000 : ℝ)|^4585 ≤ (3090673244987/10000000000000 : ℝ)^3561
        have hw : |(2008690813/5000000000 : ℝ)|=(2008690813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252169067/5000000000 : ℝ)|^4585 ≤ (35812053429423/100000000000000 : ℝ)^3561
        have hw : |(2252169067/5000000000 : ℝ)|=(2252169067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s6_4 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-455446747/2500000000 : ℝ)*x 0 + (5220184449/10000000000 : ℝ)*x 1 + (5428003521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (455446747/2500000000 : ℝ)^4585 ≤ (5582343155121/50000000000000 : ℝ)^3561 := by
    have hnat : (455446747 : ℕ)^4585*50000000000000^3561 ≤ 5582343155121^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455446747 2500000000 5582343155121 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220184449/10000000000 : ℝ)^4585 ≤ (4330157400031/10000000000000 : ℝ)^3561 := by
    have hnat : (5220184449 : ℕ)^4585*10000000000000^3561 ≤ 4330157400031^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220184449 10000000000 4330157400031 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428003521/10000000000 : ℝ)^4585 ≤ (45533739672913/100000000000000 : ℝ)^3561 := by
    have hnat : (5428003521 : ℕ)^4585*100000000000000^3561 ≤ 45533739672913^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428003521 10000000000 45533739672913 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-455446747/2500000000 : ℝ), (5220184449/10000000000 : ℝ), (5428003521/10000000000 : ℝ)] ![(5582343155121/50000000000000 : ℝ), (4330157400031/10000000000000 : ℝ), (45533739672913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-455446747/2500000000 : ℝ)|^4585 ≤ (5582343155121/50000000000000 : ℝ)^3561
        have hw : |(-455446747/2500000000 : ℝ)|=(455446747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220184449/10000000000 : ℝ)|^4585 ≤ (4330157400031/10000000000000 : ℝ)^3561
        have hw : |(5220184449/10000000000 : ℝ)|=(5220184449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428003521/10000000000 : ℝ)|^4585 ≤ (45533739672913/100000000000000 : ℝ)^3561
        have hw : |(5428003521/10000000000 : ℝ)|=(5428003521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s6_5 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132973847/312500000 : ℝ)*x 0 + (450181599/1000000000 : ℝ)*x 1 + (2009961671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132973847/312500000 : ℝ)^4585 ≤ (16640925742917/50000000000000 : ℝ)^3561 := by
    have hnat : (132973847 : ℕ)^4585*50000000000000^3561 ≤ 16640925742917^3561*312500000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132973847 312500000 16640925742917 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450181599/1000000000 : ℝ)^4585 ≤ (35786236742163/100000000000000 : ℝ)^3561 := by
    have hnat : (450181599 : ℕ)^4585*100000000000000^3561 ≤ 35786236742163^3561*1000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450181599 1000000000 35786236742163 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2009961671/5000000000 : ℝ)^4585 ≤ (30931911763731/100000000000000 : ℝ)^3561 := by
    have hnat : (2009961671 : ℕ)^4585*100000000000000^3561 ≤ 30931911763731^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009961671 5000000000 30931911763731 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132973847/312500000 : ℝ), (450181599/1000000000 : ℝ), (2009961671/5000000000 : ℝ)] ![(16640925742917/50000000000000 : ℝ), (35786236742163/100000000000000 : ℝ), (30931911763731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132973847/312500000 : ℝ)|^4585 ≤ (16640925742917/50000000000000 : ℝ)^3561
        have hw : |(132973847/312500000 : ℝ)|=(132973847/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450181599/1000000000 : ℝ)|^4585 ≤ (35786236742163/100000000000000 : ℝ)^3561
        have hw : |(450181599/1000000000 : ℝ)|=(450181599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2009961671/5000000000 : ℝ)|^4585 ≤ (30931911763731/100000000000000 : ℝ)^3561
        have hw : |(2009961671/5000000000 : ℝ)|=(2009961671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1544_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5517/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11033/100000 : ℝ) ^ (4583/1024 : ℝ) ≤ (5193893253629071/100000000000000000000 : ℝ) := by
    have hpowers : (11033/100000 : ℝ)^4583 ≤ (5193893253629071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11033 : ℕ)^4583*100000000000000000000^1024 ≤ 5193893253629071^1024*100000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11033 100000 5193893253629071 100000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11033/100000 : ℝ)) (X := (5193893253629071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4583/1024 : ℝ) ≤ (23679798471510933/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4583 ≤ (23679798471510933/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4583*100000000000000000000^1024 ≤ 23679798471510933^1024*20000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 23679798471510933 100000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (23679798471510933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005193893253629071/50000000000000000000 : ℝ) ≤ (3906340659983/3906250000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (50005193893253629071/50000000000000000000 : ℝ)^1024 ≤ (3906340659983/3906250000000 : ℝ)^4583 := by
      have hnat : (50005193893253629071 : ℕ)^1024*3906250000000^4583 ≤ 3906340659983^4583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005193893253629071 50000000000000000000 3906340659983 3906250000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3906340659983/3906250000000 : ℝ)) (X := (50005193893253629071/50000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007218422931285001/25000000000000000000 : ℝ) ≤ (10000645065374829/10000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (25007218422931285001/25000000000000000000 : ℝ)^1024 ≤ (10000645065374829/10000000000000000 : ℝ)^4583 := by
      have hnat : (25007218422931285001 : ℕ)^1024*10000000000000000^4583 ≤ 10000645065374829^4583*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007218422931285001 25000000000000000000 10000645065374829 10000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000645065374829/10000000000000000 : ℝ)) (X := (25007218422931285001/25000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023679798471510933/50000000000000000000 : ℝ) ≤ (5000529020596589/5000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (50023679798471510933/50000000000000000000 : ℝ)^1024 ≤ (5000529020596589/5000000000000000 : ℝ)^4583 := by
      have hnat : (50023679798471510933 : ℕ)^1024*5000000000000000^4583 ≤ 5000529020596589^4583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023679798471510933 50000000000000000000 5000529020596589 5000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000529020596589/5000000000000000 : ℝ)) (X := (50023679798471510933/50000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5193893253629071/100000000000000000000 : ℝ) ≤ ((22255960269148879963/22260000000000000000 : ℝ)+2*(412975818349/445200000000000 : ℝ)*(11033/100000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (22255960269148879963/22260000000000000000 : ℝ)+2*(412975818349/445200000000000 : ℝ)*(11033/100000 : ℝ)=(3906340659983/3906250000000 : ℝ) by norm_num, show 1+2*(5193893253629071/100000000000000000000 : ℝ)=(50005193893253629071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23679798471510933/100000000000000000000 : ℝ)+(5193893253629071/100000000000000000000 : ℝ) ≤ ((22255960269148879963/22260000000000000000 : ℝ)+(412975818349/445200000000000 : ℝ)*((3097/20000 : ℝ)+(11033/100000 : ℝ)))^(4583/1024 : ℝ) := by
    rw [show (22255960269148879963/22260000000000000000 : ℝ)+(412975818349/445200000000000 : ℝ)*((3097/20000 : ℝ)+(11033/100000 : ℝ))=(10000645065374829/10000000000000000 : ℝ) by norm_num, show 1+(23679798471510933/100000000000000000000 : ℝ)+(5193893253629071/100000000000000000000 : ℝ)=(25007218422931285001/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23679798471510933/100000000000000000000 : ℝ) ≤ ((22255960269148879963/22260000000000000000 : ℝ)+2*(412975818349/445200000000000 : ℝ)*(3097/20000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (22255960269148879963/22260000000000000000 : ℝ)+2*(412975818349/445200000000000 : ℝ)*(3097/20000 : ℝ)=(5000529020596589/5000000000000000 : ℝ) by norm_num, show 1+2*(23679798471510933/100000000000000000000 : ℝ)=(50023679798471510933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22255960269148879963/22260000000000000000 : ℝ)*(X 1 0+X 2 0)+(412975818349/445200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22255960269148879963/22260000000000000000 : ℝ)) (alpha := (412975818349/445200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22255960269148879963/22260000000000000000 : ℝ)*(X 0 1+X 2 1)+(412975818349/445200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22255960269148879963/22260000000000000000 : ℝ)) (alpha := (412975818349/445200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22255960269148879963/22260000000000000000 : ℝ)*(X 0 2+X 1 2)+(412975818349/445200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22255960269148879963/22260000000000000000 : ℝ)) (alpha := (412975818349/445200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-72870381/400000000 : ℝ)*X 0 0+(271454969/500000000 : ℝ)*X 0 1+(5219096443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349754803/10000000000 : ℝ)*X 1 0+(-1929245397/10000000000 : ℝ)*X 1 1+(5219096771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337438747/2500000000 : ℝ)*X 2 0+(5219096553/10000000000 : ℝ)*X 2 1+(-964622719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4255099813/10000000000 : ℝ)*X 0 0+(2008690813/5000000000 : ℝ)*X 0 1+(2252169067/5000000000 : ℝ)*X 0 2+(4255099813/10000000000 : ℝ)*X 1 0+(2008690813/5000000000 : ℝ)*X 1 1+(2252169067/5000000000 : ℝ)*X 1 2+(4255099813/10000000000 : ℝ)*X 2 0+(2008690813/5000000000 : ℝ)*X 2 1+(2252169067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-455446747/2500000000 : ℝ)*X 0 0+(5220184449/10000000000 : ℝ)*X 0 1+(5428003521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132973847/312500000 : ℝ)*X 0 0+(450181599/1000000000 : ℝ)*X 0 1+(2009961671/5000000000 : ℝ)*X 0 2+(132973847/312500000 : ℝ)*X 1 0+(450181599/1000000000 : ℝ)*X 1 1+(2009961671/5000000000 : ℝ)*X 1 2+(132973847/312500000 : ℝ)*X 2 0+(450181599/1000000000 : ℝ)*X 2 1+(2009961671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37516844514103588774083/7420000000000000000000000000 : ℝ) := by norm_num
    linear_combination (833877841/100000000000000 : ℝ)*(base19) + (343736361/50000000000000 : ℝ)*(base23) + (83208839/50000000000000 : ℝ)*(lower2) + (283739343/100000000000000 : ℝ)*(upper3) + (2705941/6250000000000 : ℝ)*(upper5) + (3407725076971611/100000000000000 : ℝ)*(major0) + (3407725076971611/100000000000000 : ℝ)*(major1) + (3407725076971611/100000000000000 : ℝ)*(major2) + (595231772565307/12500000000000 : ℝ)*(sp0) + (2380933162303657/50000000000000 : ℝ)*(sp1) + (2380933235506217/50000000000000 : ℝ)*(sp2) + (51339378459351/2500000000000 : ℝ)*(sp3) + (129779627/1000000000000 : ℝ)*(sp4) + (1922136183/25000000000000 : ℝ)*(sp5) + (513395706729693/25000000000000 : ℝ)*(f.failure) + (952373431697031/20000000000000 : ℝ)*(f.sum) + (6655752135253/7420000000000000000000000000 : ℝ)*base65 + (2503982955563439869/742000000000000000000000000000000 : ℝ)*base68 + (5649011624667439869/742000000000000000000000000000000 : ℝ)*base70 + (7068137224856560131/742000000000000000000000000000000 : ℝ)*base71 + (11790849103373/7420000000000000000000000000 : ℝ)*base73 + (2258859024920560131/742000000000000000000000000000000 : ℝ)*base75 + (1124352779443439869/742000000000000000000000000000000 : ℝ)*base78 + (6012833711312560131/742000000000000000000000000000000 : ℝ)*base79 + (11957208842373/7420000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (14352759/1250000000000000000000 : ℝ)*base90 + (14352759/1250000000000000000000 : ℝ)*base92 + (14352759/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1544_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1544_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1544_box_0 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1613681053/10000000000 : ℝ)*x 0 + (1079876431/2000000000 : ℝ)*x 1 + (5399382451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1613681053/10000000000 : ℝ)^4585 ≤ (2387580505547/25000000000000 : ℝ)^3561 := by
    have hnat : (1613681053 : ℕ)^4585*25000000000000^3561 ≤ 2387580505547^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613681053 10000000000 2387580505547 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079876431/2000000000 : ℝ)^4585 ≤ (5653104672707/12500000000000 : ℝ)^3561 := by
    have hnat : (1079876431 : ℕ)^4585*12500000000000^3561 ≤ 5653104672707^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079876431 2000000000 5653104672707 12500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399382451/10000000000 : ℝ)^4585 ≤ (4522484057387/10000000000000 : ℝ)^3561 := by
    have hnat : (5399382451 : ℕ)^4585*10000000000000^3561 ≤ 4522484057387^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399382451 10000000000 4522484057387 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1613681053/10000000000 : ℝ), (1079876431/2000000000 : ℝ), (5399382451/10000000000 : ℝ)] ![(2387580505547/25000000000000 : ℝ), (5653104672707/12500000000000 : ℝ), (4522484057387/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1613681053/10000000000 : ℝ)|^4585 ≤ (2387580505547/25000000000000 : ℝ)^3561
        have hw : |(-1613681053/10000000000 : ℝ)|=(1613681053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079876431/2000000000 : ℝ)|^4585 ≤ (5653104672707/12500000000000 : ℝ)^3561
        have hw : |(1079876431/2000000000 : ℝ)|=(1079876431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399382451/10000000000 : ℝ)|^4585 ≤ (4522484057387/10000000000000 : ℝ)^3561
        have hw : |(5399382451/10000000000 : ℝ)|=(5399382451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_1 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658883771/1250000000 : ℝ)*x 0 + (-44797281/250000000 : ℝ)*x 1 + (2699691329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658883771/1250000000 : ℝ)^4585 ≤ (21922905443467/50000000000000 : ℝ)^3561 := by
    have hnat : (658883771 : ℕ)^4585*50000000000000^3561 ≤ 21922905443467^3561*1250000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658883771 1250000000 21922905443467 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44797281/250000000 : ℝ)^4585 ≤ (2185869258247/20000000000000 : ℝ)^3561 := by
    have hnat : (44797281 : ℕ)^4585*20000000000000^3561 ≤ 2185869258247^3561*250000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44797281 250000000 2185869258247 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699691329/5000000000 : ℝ)^4585 ≤ (45224842806263/100000000000000 : ℝ)^3561 := by
    have hnat : (2699691329 : ℕ)^4585*100000000000000^3561 ≤ 45224842806263^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699691329 5000000000 45224842806263 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658883771/1250000000 : ℝ), (-44797281/250000000 : ℝ), (2699691329/5000000000 : ℝ)] ![(21922905443467/50000000000000 : ℝ), (2185869258247/20000000000000 : ℝ), (45224842806263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658883771/1250000000 : ℝ)|^4585 ≤ (21922905443467/50000000000000 : ℝ)^3561
        have hw : |(658883771/1250000000 : ℝ)|=(658883771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44797281/250000000 : ℝ)|^4585 ≤ (2185869258247/20000000000000 : ℝ)^3561
        have hw : |(-44797281/250000000 : ℝ)|=(44797281/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699691329/5000000000 : ℝ)|^4585 ≤ (45224842806263/100000000000000 : ℝ)^3561
        have hw : |(2699691329/5000000000 : ℝ)|=(2699691329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_2 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635534871/5000000000 : ℝ)*x 0 + (5399383483/10000000000 : ℝ)*x 1 + (-6999573/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635534871/5000000000 : ℝ)^4585 ≤ (43845806324399/100000000000000 : ℝ)^3561 := by
    have hnat : (2635534871 : ℕ)^4585*100000000000000^3561 ≤ 43845806324399^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635534871 5000000000 43845806324399 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399383483/10000000000 : ℝ)^4585 ≤ (22612425851741/50000000000000 : ℝ)^3561 := by
    have hnat : (5399383483 : ℕ)^4585*50000000000000^3561 ≤ 22612425851741^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399383483 10000000000 22612425851741 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6999573/39062500 : ℝ)^4585 ≤ (2732335489059/25000000000000 : ℝ)^3561 := by
    have hnat : (6999573 : ℕ)^4585*25000000000000^3561 ≤ 2732335489059^3561*39062500^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6999573 39062500 2732335489059 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635534871/5000000000 : ℝ), (5399383483/10000000000 : ℝ), (-6999573/39062500 : ℝ)] ![(43845806324399/100000000000000 : ℝ), (22612425851741/50000000000000 : ℝ), (2732335489059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635534871/5000000000 : ℝ)|^4585 ≤ (43845806324399/100000000000000 : ℝ)^3561
        have hw : |(2635534871/5000000000 : ℝ)|=(2635534871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399383483/10000000000 : ℝ)|^4585 ≤ (22612425851741/50000000000000 : ℝ)^3561
        have hw : |(5399383483/10000000000 : ℝ)|=(5399383483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6999573/39062500 : ℝ)|^4585 ≤ (2732335489059/25000000000000 : ℝ)^3561
        have hw : |(-6999573/39062500 : ℝ)|=(6999573/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_3 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2228395399/5000000000 : ℝ)*x 0 + (260064791/625000000 : ℝ)*x 1 + (4161037599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2228395399/5000000000 : ℝ)^4585 ≤ (3532605989503/10000000000000 : ℝ)^3561 := by
    have hnat : (2228395399 : ℕ)^4585*10000000000000^3561 ≤ 3532605989503^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228395399 5000000000 3532605989503 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260064791/625000000 : ℝ)^4585 ≤ (32336965330559/100000000000000 : ℝ)^3561 := by
    have hnat : (260064791 : ℕ)^4585*100000000000000^3561 ≤ 32336965330559^3561*625000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260064791 625000000 32336965330559 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4161037599/10000000000 : ℝ)^4585 ≤ (32336974766317/100000000000000 : ℝ)^3561 := by
    have hnat : (4161037599 : ℕ)^4585*100000000000000^3561 ≤ 32336974766317^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161037599 10000000000 32336974766317 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2228395399/5000000000 : ℝ), (260064791/625000000 : ℝ), (4161037599/10000000000 : ℝ)] ![(3532605989503/10000000000000 : ℝ), (32336965330559/100000000000000 : ℝ), (32336974766317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2228395399/5000000000 : ℝ)|^4585 ≤ (3532605989503/10000000000000 : ℝ)^3561
        have hw : |(2228395399/5000000000 : ℝ)|=(2228395399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260064791/625000000 : ℝ)|^4585 ≤ (32336965330559/100000000000000 : ℝ)^3561
        have hw : |(260064791/625000000 : ℝ)|=(260064791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4161037599/10000000000 : ℝ)|^4585 ≤ (32336974766317/100000000000000 : ℝ)^3561
        have hw : |(4161037599/10000000000 : ℝ)|=(4161037599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_4 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-203524761/1000000000 : ℝ)*x 0 + (2622260211/5000000000 : ℝ)*x 1 + (2622260403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203524761/1000000000 : ℝ)^4585 ≤ (1287666674401/10000000000000 : ℝ)^3561 := by
    have hnat : (203524761 : ℕ)^4585*10000000000000^3561 ≤ 1287666674401^3561*1000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203524761 1000000000 1287666674401 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622260211/5000000000 : ℝ)^4585 ≤ (43561664565747/100000000000000 : ℝ)^3561 := by
    have hnat : (2622260211 : ℕ)^4585*100000000000000^3561 ≤ 43561664565747^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622260211 5000000000 43561664565747 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622260403/5000000000 : ℝ)^4585 ≤ (5445208584061/12500000000000 : ℝ)^3561 := by
    have hnat : (2622260403 : ℕ)^4585*12500000000000^3561 ≤ 5445208584061^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622260403 5000000000 5445208584061 12500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203524761/1000000000 : ℝ), (2622260211/5000000000 : ℝ), (2622260403/5000000000 : ℝ)] ![(1287666674401/10000000000000 : ℝ), (43561664565747/100000000000000 : ℝ), (5445208584061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203524761/1000000000 : ℝ)|^4585 ≤ (1287666674401/10000000000000 : ℝ)^3561
        have hw : |(-203524761/1000000000 : ℝ)|=(203524761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622260211/5000000000 : ℝ)|^4585 ≤ (43561664565747/100000000000000 : ℝ)^3561
        have hw : |(2622260211/5000000000 : ℝ)|=(2622260211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622260403/5000000000 : ℝ)|^4585 ≤ (5445208584061/12500000000000 : ℝ)^3561
        have hw : |(2622260403/5000000000 : ℝ)|=(2622260403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_5 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344656531/2500000000 : ℝ)*x 0 + (-92811601/500000000 : ℝ)*x 1 + (5244520421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344656531/2500000000 : ℝ)^4585 ≤ (45001117645401/100000000000000 : ℝ)^3561 := by
    have hnat : (1344656531 : ℕ)^4585*100000000000000^3561 ≤ 45001117645401^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344656531 2500000000 45001117645401 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92811601/500000000 : ℝ)^4585 ≤ (5718608892181/50000000000000 : ℝ)^3561 := by
    have hnat : (92811601 : ℕ)^4585*50000000000000^3561 ≤ 5718608892181^3561*500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92811601 500000000 5718608892181 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244520421/10000000000 : ℝ)^4585 ≤ (10890416138763/25000000000000 : ℝ)^3561 := by
    have hnat : (5244520421 : ℕ)^4585*25000000000000^3561 ≤ 10890416138763^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244520421 10000000000 10890416138763 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344656531/2500000000 : ℝ), (-92811601/500000000 : ℝ), (5244520421/10000000000 : ℝ)] ![(45001117645401/100000000000000 : ℝ), (5718608892181/50000000000000 : ℝ), (10890416138763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344656531/2500000000 : ℝ)|^4585 ≤ (45001117645401/100000000000000 : ℝ)^3561
        have hw : |(1344656531/2500000000 : ℝ)|=(1344656531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92811601/500000000 : ℝ)|^4585 ≤ (5718608892181/50000000000000 : ℝ)^3561
        have hw : |(-92811601/500000000 : ℝ)|=(92811601/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244520421/10000000000 : ℝ)|^4585 ≤ (10890416138763/25000000000000 : ℝ)^3561
        have hw : |(5244520421/10000000000 : ℝ)|=(5244520421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_6 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378625729/10000000000 : ℝ)*x 0 + (1311130187/2500000000 : ℝ)*x 1 + (-371246423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378625729/10000000000 : ℝ)^4585 ≤ (11250278347559/25000000000000 : ℝ)^3561 := by
    have hnat : (5378625729 : ℕ)^4585*25000000000000^3561 ≤ 11250278347559^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378625729 10000000000 11250278347559 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311130187/2500000000 : ℝ)^4585 ≤ (43561668052199/100000000000000 : ℝ)^3561 := by
    have hnat : (1311130187 : ℕ)^4585*100000000000000^3561 ≤ 43561668052199^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311130187 2500000000 43561668052199 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371246423/2000000000 : ℝ)^4585 ≤ (11437218538029/100000000000000 : ℝ)^3561 := by
    have hnat : (371246423 : ℕ)^4585*100000000000000^3561 ≤ 11437218538029^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371246423 2000000000 11437218538029 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378625729/10000000000 : ℝ), (1311130187/2500000000 : ℝ), (-371246423/2000000000 : ℝ)] ![(11250278347559/25000000000000 : ℝ), (43561668052199/100000000000000 : ℝ), (11437218538029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378625729/10000000000 : ℝ)|^4585 ≤ (11250278347559/25000000000000 : ℝ)^3561
        have hw : |(5378625729/10000000000 : ℝ)|=(5378625729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311130187/2500000000 : ℝ)|^4585 ≤ (43561668052199/100000000000000 : ℝ)^3561
        have hw : |(1311130187/2500000000 : ℝ)|=(1311130187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-371246423/2000000000 : ℝ)|^4585 ≤ (11437218538029/100000000000000 : ℝ)^3561
        have hw : |(-371246423/2000000000 : ℝ)|=(371246423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_7 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2025417991/5000000000 : ℝ)*x 0 + (4363884287/10000000000 : ℝ)*x 1 + (2181942037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025417991/5000000000 : ℝ)^4585 ≤ (31238511298641/100000000000000 : ℝ)^3561 := by
    have hnat : (2025417991 : ℕ)^4585*100000000000000^3561 ≤ 31238511298641^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025417991 5000000000 31238511298641 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4363884287/10000000000 : ℝ)^4585 ≤ (17190372710991/50000000000000 : ℝ)^3561 := by
    have hnat : (4363884287 : ℕ)^4585*50000000000000^3561 ≤ 17190372710991^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363884287 10000000000 17190372710991 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181942037/5000000000 : ℝ)^4585 ≤ (34380743261309/100000000000000 : ℝ)^3561 := by
    have hnat : (2181942037 : ℕ)^4585*100000000000000^3561 ≤ 34380743261309^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181942037 5000000000 34380743261309 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2025417991/5000000000 : ℝ), (4363884287/10000000000 : ℝ), (2181942037/5000000000 : ℝ)] ![(31238511298641/100000000000000 : ℝ), (17190372710991/50000000000000 : ℝ), (34380743261309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2025417991/5000000000 : ℝ)|^4585 ≤ (31238511298641/100000000000000 : ℝ)^3561
        have hw : |(2025417991/5000000000 : ℝ)|=(2025417991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4363884287/10000000000 : ℝ)|^4585 ≤ (17190372710991/50000000000000 : ℝ)^3561
        have hw : |(4363884287/10000000000 : ℝ)|=(4363884287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2181942037/5000000000 : ℝ)|^4585 ≤ (34380743261309/100000000000000 : ℝ)^3561
        have hw : |(2181942037/5000000000 : ℝ)|=(2181942037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_8 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-486500931/2500000000 : ℝ)*x 0 + (2567843561/5000000000 : ℝ)*x 1 + (5419737181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486500931/2500000000 : ℝ)^4585 ≤ (3038575698327/25000000000000 : ℝ)^3561 := by
    have hnat : (486500931 : ℕ)^4585*25000000000000^3561 ≤ 3038575698327^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486500931 2500000000 3038575698327 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567843561/5000000000 : ℝ)^4585 ≤ (1325038187613/3125000000000 : ℝ)^3561 := by
    have hnat : (2567843561 : ℕ)^4585*3125000000000^3561 ≤ 1325038187613^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567843561 5000000000 1325038187613 3125000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419737181/10000000000 : ℝ)^4585 ≤ (11361118797649/25000000000000 : ℝ)^3561 := by
    have hnat : (5419737181 : ℕ)^4585*25000000000000^3561 ≤ 11361118797649^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419737181 10000000000 11361118797649 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486500931/2500000000 : ℝ), (2567843561/5000000000 : ℝ), (5419737181/10000000000 : ℝ)] ![(3038575698327/25000000000000 : ℝ), (1325038187613/3125000000000 : ℝ), (11361118797649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486500931/2500000000 : ℝ)|^4585 ≤ (3038575698327/25000000000000 : ℝ)^3561
        have hw : |(-486500931/2500000000 : ℝ)|=(486500931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567843561/5000000000 : ℝ)|^4585 ≤ (1325038187613/3125000000000 : ℝ)^3561
        have hw : |(2567843561/5000000000 : ℝ)|=(2567843561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419737181/10000000000 : ℝ)|^4585 ≤ (11361118797649/25000000000000 : ℝ)^3561
        have hw : |(5419737181/10000000000 : ℝ)|=(5419737181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_9 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256929279/10000000000 : ℝ)*x 0 + (-1783195987/10000000000 : ℝ)*x 1 + (1083947417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256929279/10000000000 : ℝ)^4585 ≤ (21847208954509/50000000000000 : ℝ)^3561 := by
    have hnat : (5256929279 : ℕ)^4585*50000000000000^3561 ≤ 21847208954509^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256929279 10000000000 21847208954509 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1783195987/10000000000 : ℝ)^4585 ≤ (5430553958883/50000000000000 : ℝ)^3561 := by
    have hnat : (1783195987 : ℕ)^4585*50000000000000^3561 ≤ 5430553958883^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783195987 10000000000 5430553958883 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083947417/2000000000 : ℝ)^4585 ≤ (22722237077081/50000000000000 : ℝ)^3561 := by
    have hnat : (1083947417 : ℕ)^4585*50000000000000^3561 ≤ 22722237077081^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083947417 2000000000 22722237077081 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256929279/10000000000 : ℝ), (-1783195987/10000000000 : ℝ), (1083947417/2000000000 : ℝ)] ![(21847208954509/50000000000000 : ℝ), (5430553958883/50000000000000 : ℝ), (22722237077081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256929279/10000000000 : ℝ)|^4585 ≤ (21847208954509/50000000000000 : ℝ)^3561
        have hw : |(5256929279/10000000000 : ℝ)|=(5256929279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1783195987/10000000000 : ℝ)|^4585 ≤ (5430553958883/50000000000000 : ℝ)^3561
        have hw : |(-1783195987/10000000000 : ℝ)|=(1783195987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083947417/2000000000 : ℝ)|^4585 ≤ (22722237077081/50000000000000 : ℝ)^3561
        have hw : |(1083947417/2000000000 : ℝ)|=(1083947417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_10 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262846467/500000000 : ℝ)*x 0 + (2709868527/5000000000 : ℝ)*x 1 + (-1783195947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262846467/500000000 : ℝ)^4585 ≤ (8738883712367/20000000000000 : ℝ)^3561 := by
    have hnat : (262846467 : ℕ)^4585*20000000000000^3561 ≤ 8738883712367^3561*500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262846467 500000000 8738883712367 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709868527/5000000000 : ℝ)^4585 ≤ (1136111845487/2500000000000 : ℝ)^3561 := by
    have hnat : (2709868527 : ℕ)^4585*2500000000000^3561 ≤ 1136111845487^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709868527 5000000000 1136111845487 2500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783195947/10000000000 : ℝ)^4585 ≤ (5430553802037/50000000000000 : ℝ)^3561 := by
    have hnat : (1783195947 : ℕ)^4585*50000000000000^3561 ≤ 5430553802037^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783195947 10000000000 5430553802037 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262846467/500000000 : ℝ), (2709868527/5000000000 : ℝ), (-1783195947/10000000000 : ℝ)] ![(8738883712367/20000000000000 : ℝ), (1136111845487/2500000000000 : ℝ), (5430553802037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262846467/500000000 : ℝ)|^4585 ≤ (8738883712367/20000000000000 : ℝ)^3561
        have hw : |(262846467/500000000 : ℝ)|=(262846467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709868527/5000000000 : ℝ)|^4585 ≤ (1136111845487/2500000000000 : ℝ)^3561
        have hw : |(2709868527/5000000000 : ℝ)|=(2709868527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1783195947/10000000000 : ℝ)|^4585 ≤ (5430553802037/50000000000000 : ℝ)^3561
        have hw : |(-1783195947/10000000000 : ℝ)|=(1783195947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_11 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4509001003/10000000000 : ℝ)*x 0 + (1033585499/2500000000 : ℝ)*x 1 + (206717107/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4509001003/10000000000 : ℝ)^4585 ≤ (17929896771033/50000000000000 : ℝ)^3561 := by
    have hnat : (4509001003 : ℕ)^4585*50000000000000^3561 ≤ 17929896771033^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509001003 10000000000 17929896771033 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033585499/2500000000 : ℝ)^4585 ≤ (32070102500489/100000000000000 : ℝ)^3561 := by
    have hnat : (1033585499 : ℕ)^4585*100000000000000^3561 ≤ 32070102500489^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033585499 2500000000 32070102500489 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206717107/500000000 : ℝ)^4585 ≤ (2004381496169/6250000000000 : ℝ)^3561 := by
    have hnat : (206717107 : ℕ)^4585*6250000000000^3561 ≤ 2004381496169^3561*500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206717107 500000000 2004381496169 6250000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4509001003/10000000000 : ℝ), (1033585499/2500000000 : ℝ), (206717107/500000000 : ℝ)] ![(17929896771033/50000000000000 : ℝ), (32070102500489/100000000000000 : ℝ), (2004381496169/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4509001003/10000000000 : ℝ)|^4585 ≤ (17929896771033/50000000000000 : ℝ)^3561
        have hw : |(4509001003/10000000000 : ℝ)|=(4509001003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033585499/2500000000 : ℝ)|^4585 ≤ (32070102500489/100000000000000 : ℝ)^3561
        have hw : |(1033585499/2500000000 : ℝ)|=(1033585499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206717107/500000000 : ℝ)|^4585 ≤ (2004381496169/6250000000000 : ℝ)^3561
        have hw : |(206717107/500000000 : ℝ)|=(206717107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_12 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1702709373/10000000000 : ℝ)*x 0 + (5504820283/10000000000 : ℝ)*x 1 + (5229475977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1702709373/10000000000 : ℝ)^4585 ≤ (2558512574169/25000000000000 : ℝ)^3561 := by
    have hnat : (1702709373 : ℕ)^4585*25000000000000^3561 ≤ 2558512574169^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702709373 10000000000 2558512574169 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504820283/10000000000 : ℝ)^4585 ≤ (23182556804551/50000000000000 : ℝ)^3561 := by
    have hnat : (5504820283 : ℕ)^4585*50000000000000^3561 ≤ 23182556804551^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504820283 10000000000 23182556804551 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229475977/10000000000 : ℝ)^4585 ≤ (1085020902303/2500000000000 : ℝ)^3561 := by
    have hnat : (5229475977 : ℕ)^4585*2500000000000^3561 ≤ 1085020902303^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229475977 10000000000 1085020902303 2500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1702709373/10000000000 : ℝ), (5504820283/10000000000 : ℝ), (5229475977/10000000000 : ℝ)] ![(2558512574169/25000000000000 : ℝ), (23182556804551/50000000000000 : ℝ), (1085020902303/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1702709373/10000000000 : ℝ)|^4585 ≤ (2558512574169/25000000000000 : ℝ)^3561
        have hw : |(-1702709373/10000000000 : ℝ)|=(1702709373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504820283/10000000000 : ℝ)|^4585 ≤ (23182556804551/50000000000000 : ℝ)^3561
        have hw : |(5504820283/10000000000 : ℝ)|=(5504820283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229475977/10000000000 : ℝ)|^4585 ≤ (1085020902303/2500000000000 : ℝ)^3561
        have hw : |(5229475977/10000000000 : ℝ)|=(5229475977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_13 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389075487/10000000000 : ℝ)*x 0 + (-465577277/2500000000 : ℝ)*x 1 + (5229475633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389075487/10000000000 : ℝ)^4585 ≤ (9022743112883/20000000000000 : ℝ)^3561 := by
    have hnat : (5389075487 : ℕ)^4585*20000000000000^3561 ≤ 9022743112883^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389075487 10000000000 9022743112883 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465577277/2500000000 : ℝ)^4585 ≤ (287136300071/2500000000000 : ℝ)^3561 := by
    have hnat : (465577277 : ℕ)^4585*2500000000000^3561 ≤ 287136300071^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465577277 2500000000 287136300071 2500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229475633/10000000000 : ℝ)^4585 ≤ (43400832416203/100000000000000 : ℝ)^3561 := by
    have hnat : (5229475633 : ℕ)^4585*100000000000000^3561 ≤ 43400832416203^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229475633 10000000000 43400832416203 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389075487/10000000000 : ℝ), (-465577277/2500000000 : ℝ), (5229475633/10000000000 : ℝ)] ![(9022743112883/20000000000000 : ℝ), (287136300071/2500000000000 : ℝ), (43400832416203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389075487/10000000000 : ℝ)|^4585 ≤ (9022743112883/20000000000000 : ℝ)^3561
        have hw : |(5389075487/10000000000 : ℝ)|=(5389075487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-465577277/2500000000 : ℝ)|^4585 ≤ (287136300071/2500000000000 : ℝ)^3561
        have hw : |(-465577277/2500000000 : ℝ)|=(465577277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229475633/10000000000 : ℝ)|^4585 ≤ (43400832416203/100000000000000 : ℝ)^3561
        have hw : |(5229475633/10000000000 : ℝ)|=(5229475633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_14 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84204307/156250000 : ℝ)*x 0 + (5229475411/10000000000 : ℝ)*x 1 + (-465577297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84204307/156250000 : ℝ)^4585 ≤ (45113717299767/100000000000000 : ℝ)^3561 := by
    have hnat : (84204307 : ℕ)^4585*100000000000000^3561 ≤ 45113717299767^3561*156250000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84204307 156250000 45113717299767 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229475411/10000000000 : ℝ)^4585 ≤ (21700415021977/50000000000000 : ℝ)^3561 := by
    have hnat : (5229475411 : ℕ)^4585*50000000000000^3561 ≤ 21700415021977^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229475411 10000000000 21700415021977 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465577297/2500000000 : ℝ)^4585 ≤ (1435681579763/12500000000000 : ℝ)^3561 := by
    have hnat : (465577297 : ℕ)^4585*12500000000000^3561 ≤ 1435681579763^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465577297 2500000000 1435681579763 12500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84204307/156250000 : ℝ), (5229475411/10000000000 : ℝ), (-465577297/2500000000 : ℝ)] ![(45113717299767/100000000000000 : ℝ), (21700415021977/50000000000000 : ℝ), (1435681579763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84204307/156250000 : ℝ)|^4585 ≤ (45113717299767/100000000000000 : ℝ)^3561
        have hw : |(84204307/156250000 : ℝ)|=(84204307/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229475411/10000000000 : ℝ)|^4585 ≤ (21700415021977/50000000000000 : ℝ)^3561
        have hw : |(5229475411/10000000000 : ℝ)|=(5229475411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-465577297/2500000000 : ℝ)|^4585 ≤ (1435681579763/12500000000000 : ℝ)^3561
        have hw : |(-465577297/2500000000 : ℝ)|=(465577297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_box_15 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2005267251/5000000000 : ℝ)*x 0 + (4383567389/10000000000 : ℝ)*x 1 + (4383566873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005267251/5000000000 : ℝ)^4585 ≤ (3083892473937/10000000000000 : ℝ)^3561 := by
    have hnat : (2005267251 : ℕ)^4585*10000000000000^3561 ≤ 3083892473937^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005267251 5000000000 3083892473937 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4383567389/10000000000 : ℝ)^4585 ≤ (108064188257/312500000000 : ℝ)^3561 := by
    have hnat : (4383567389 : ℕ)^4585*312500000000^3561 ≤ 108064188257^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383567389 10000000000 108064188257 312500000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4383566873/10000000000 : ℝ)^4585 ≤ (8645133750289/25000000000000 : ℝ)^3561 := by
    have hnat : (4383566873 : ℕ)^4585*25000000000000^3561 ≤ 8645133750289^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383566873 10000000000 8645133750289 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2005267251/5000000000 : ℝ), (4383567389/10000000000 : ℝ), (4383566873/10000000000 : ℝ)] ![(3083892473937/10000000000000 : ℝ), (108064188257/312500000000 : ℝ), (8645133750289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2005267251/5000000000 : ℝ)|^4585 ≤ (3083892473937/10000000000000 : ℝ)^3561
        have hw : |(2005267251/5000000000 : ℝ)|=(2005267251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4383567389/10000000000 : ℝ)|^4585 ≤ (108064188257/312500000000 : ℝ)^3561
        have hw : |(4383567389/10000000000 : ℝ)|=(4383567389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4383566873/10000000000 : ℝ)|^4585 ≤ (8645133750289/25000000000000 : ℝ)^3561
        have hw : |(4383566873/10000000000 : ℝ)|=(4383566873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1544_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12757/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58779/100000 : ℝ) ∧ (5041/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17241/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5517/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5517/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5517/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5517/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5517/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5517/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5517/50000 : ℝ) ^ (4583/1024 : ℝ) ≤ (1039200102321609/20000000000000000000 : ℝ) := by
    have hpowers : (5517/50000 : ℝ)^4583 ≤ (1039200102321609/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5517 : ℕ)^4583*20000000000000000000^1024 ≤ 1039200102321609^1024*50000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5517 50000 1039200102321609 20000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5517/50000 : ℝ)) (X := (1039200102321609/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4583/1024 : ℝ) ≤ (23679798471510933/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4583 ≤ (23679798471510933/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4583*100000000000000000000^1024 ≤ 23679798471510933^1024*20000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 23679798471510933 100000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (23679798471510933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001039200102321609/10000000000000000000 : ℝ) ≤ (62501451148223/62500000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (10001039200102321609/10000000000000000000 : ℝ)^1024 ≤ (62501451148223/62500000000000 : ℝ)^4583 := by
      have hnat : (10001039200102321609 : ℕ)^1024*62500000000000^4583 ≤ 62501451148223^4583*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001039200102321609 10000000000000000000 62501451148223 62500000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62501451148223/62500000000000 : ℝ)) (X := (10001039200102321609/10000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014437899491559489/50000000000000000000 : ℝ) ≤ (10000645112447673/10000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (50014437899491559489/50000000000000000000 : ℝ)^1024 ≤ (10000645112447673/10000000000000000 : ℝ)^4583 := by
      have hnat : (50014437899491559489 : ℕ)^1024*10000000000000000^4583 ≤ 10000645112447673^4583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014437899491559489 50000000000000000000 10000645112447673 10000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000645112447673/10000000000000000 : ℝ)) (X := (50014437899491559489/50000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023679798471510933/50000000000000000000 : ℝ) ≤ (5000529020589833/5000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (50023679798471510933/50000000000000000000 : ℝ)^1024 ≤ (5000529020589833/5000000000000000 : ℝ)^4583 := by
      have hnat : (50023679798471510933 : ℕ)^1024*5000000000000000^4583 ≤ 5000529020589833^4583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023679798471510933 50000000000000000000 5000529020589833 5000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000529020589833/5000000000000000 : ℝ)) (X := (50023679798471510933/50000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1039200102321609/20000000000000000000 : ℝ) ≤ ((11125480234615217539/11127500000000000000 : ℝ)+2*(412928731993/445100000000000 : ℝ)*(5517/50000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (11125480234615217539/11127500000000000000 : ℝ)+2*(412928731993/445100000000000 : ℝ)*(5517/50000 : ℝ)=(62501451148223/62500000000000 : ℝ) by norm_num, show 1+2*(1039200102321609/20000000000000000000 : ℝ)=(10001039200102321609/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23679798471510933/100000000000000000000 : ℝ)+(1039200102321609/20000000000000000000 : ℝ) ≤ ((11125480234615217539/11127500000000000000 : ℝ)+(412928731993/445100000000000 : ℝ)*((3097/20000 : ℝ)+(5517/50000 : ℝ)))^(4583/1024 : ℝ) := by
    rw [show (11125480234615217539/11127500000000000000 : ℝ)+(412928731993/445100000000000 : ℝ)*((3097/20000 : ℝ)+(5517/50000 : ℝ))=(10000645112447673/10000000000000000 : ℝ) by norm_num, show 1+(23679798471510933/100000000000000000000 : ℝ)+(1039200102321609/20000000000000000000 : ℝ)=(50014437899491559489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23679798471510933/100000000000000000000 : ℝ) ≤ ((11125480234615217539/11127500000000000000 : ℝ)+2*(412928731993/445100000000000 : ℝ)*(3097/20000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (11125480234615217539/11127500000000000000 : ℝ)+2*(412928731993/445100000000000 : ℝ)*(3097/20000 : ℝ)=(5000529020589833/5000000000000000 : ℝ) by norm_num, show 1+2*(23679798471510933/100000000000000000000 : ℝ)=(50023679798471510933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11125480234615217539/11127500000000000000 : ℝ)*(X 1 0+X 2 0)+(412928731993/445100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (11125480234615217539/11127500000000000000 : ℝ)) (alpha := (412928731993/445100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11125480234615217539/11127500000000000000 : ℝ)*(X 0 1+X 2 1)+(412928731993/445100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (11125480234615217539/11127500000000000000 : ℝ)) (alpha := (412928731993/445100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11125480234615217539/11127500000000000000 : ℝ)*(X 0 2+X 1 2)+(412928731993/445100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (11125480234615217539/11127500000000000000 : ℝ)) (alpha := (412928731993/445100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1613681053/10000000000 : ℝ)*X 0 0+(1079876431/2000000000 : ℝ)*X 0 1+(5399382451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((658883771/1250000000 : ℝ)*X 1 0+(-44797281/250000000 : ℝ)*X 1 1+(2699691329/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635534871/5000000000 : ℝ)*X 2 0+(5399383483/10000000000 : ℝ)*X 2 1+(-6999573/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2228395399/5000000000 : ℝ)*X 0 0+(260064791/625000000 : ℝ)*X 0 1+(4161037599/10000000000 : ℝ)*X 0 2+(2228395399/5000000000 : ℝ)*X 1 0+(260064791/625000000 : ℝ)*X 1 1+(4161037599/10000000000 : ℝ)*X 1 2+(2228395399/5000000000 : ℝ)*X 2 0+(260064791/625000000 : ℝ)*X 2 1+(4161037599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-203524761/1000000000 : ℝ)*X 0 0+(2622260211/5000000000 : ℝ)*X 0 1+(2622260403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1344656531/2500000000 : ℝ)*X 1 0+(-92811601/500000000 : ℝ)*X 1 1+(5244520421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5378625729/10000000000 : ℝ)*X 2 0+(1311130187/2500000000 : ℝ)*X 2 1+(-371246423/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2025417991/5000000000 : ℝ)*X 0 0+(4363884287/10000000000 : ℝ)*X 0 1+(2181942037/5000000000 : ℝ)*X 0 2+(2025417991/5000000000 : ℝ)*X 1 0+(4363884287/10000000000 : ℝ)*X 1 1+(2181942037/5000000000 : ℝ)*X 1 2+(2025417991/5000000000 : ℝ)*X 2 0+(4363884287/10000000000 : ℝ)*X 2 1+(2181942037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-486500931/2500000000 : ℝ)*X 0 0+(2567843561/5000000000 : ℝ)*X 0 1+(5419737181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256929279/10000000000 : ℝ)*X 1 0+(-1783195987/10000000000 : ℝ)*X 1 1+(1083947417/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((262846467/500000000 : ℝ)*X 2 0+(2709868527/5000000000 : ℝ)*X 2 1+(-1783195947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4509001003/10000000000 : ℝ)*X 0 0+(1033585499/2500000000 : ℝ)*X 0 1+(206717107/500000000 : ℝ)*X 0 2+(4509001003/10000000000 : ℝ)*X 1 0+(1033585499/2500000000 : ℝ)*X 1 1+(206717107/500000000 : ℝ)*X 1 2+(4509001003/10000000000 : ℝ)*X 2 0+(1033585499/2500000000 : ℝ)*X 2 1+(206717107/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1702709373/10000000000 : ℝ)*X 0 0+(5504820283/10000000000 : ℝ)*X 0 1+(5229475977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5389075487/10000000000 : ℝ)*X 1 0+(-465577277/2500000000 : ℝ)*X 1 1+(5229475633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((84204307/156250000 : ℝ)*X 2 0+(5229475411/10000000000 : ℝ)*X 2 1+(-465577297/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2005267251/5000000000 : ℝ)*X 0 0+(4383567389/10000000000 : ℝ)*X 0 1+(4383566873/10000000000 : ℝ)*X 0 2+(2005267251/5000000000 : ℝ)*X 1 0+(4383567389/10000000000 : ℝ)*X 1 1+(4383566873/10000000000 : ℝ)*X 1 2+(2005267251/5000000000 : ℝ)*X 2 0+(4383567389/10000000000 : ℝ)*X 2 1+(4383566873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12757/20000 : ℝ) ≤ (-35487176710539204571633018761309/55637500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2494623/10000000000000 : ℝ)*(lower0) + (53207429/100000000000000 : ℝ)*(upper1) + (11866777/12500000000000 : ℝ)*(lower4) + (227025673601977/10000000000000 : ℝ)*(major0) + (227025673601977/10000000000000 : ℝ)*(major1) + (227025673601977/10000000000000 : ℝ)*(major2) + (517132927/12500000000000 : ℝ)*(sp1) + (246964511/20000000000000 : ℝ)*(sp2) + (1042980993/100000000000000 : ℝ)*(sp3) + (798413877368763/25000000000000 : ℝ)*(sp4) + (798413787109007/25000000000000 : ℝ)*(sp5) + (399207256334611/12500000000000 : ℝ)*(sp6) + (342028522422469/25000000000000 : ℝ)*(sp7) + (3776024393/100000000000000 : ℝ)*(sp12) + (136811513267087/10000000000000 : ℝ)*(f.failure) + (798414821374861/25000000000000 : ℝ)*(f.sum) + (1152852798267/890200000000000000000000000 : ℝ)*base65 + (186198160373825397/111275000000000000000000000000000 : ℝ)*base68 + (251079594251899603/111275000000000000000000000000000 : ℝ)*base69 + (427415323108150397/111275000000000000000000000000000 : ℝ)*base72 + (710698107951/2225500000000000000000000000 : ℝ)*base73 + (657975699502074603/111275000000000000000000000000000 : ℝ)*base75 + (805877459849299603/111275000000000000000000000000000 : ℝ)*base77 + (919846839205524603/111275000000000000000000000000000 : ℝ)*base79 + (120871950299/4451000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (2689619/500000000000000000000 : ℝ)*base89 + (2689619/500000000000000000000 : ℝ)*base91 + (2689619/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58779/100000 : ℝ) ≤ (40880554497521243512270313396991/69546875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31841791/100000000000000 : ℝ)*(upper0) + (10578199/12500000000000 : ℝ)*(upper2) + (41646513/50000000000000 : ℝ)*(upper4) + (3987401/2000000000000 : ℝ)*(upper5) + (146793155406613/6250000000000 : ℝ)*(major0) + (146793155406613/6250000000000 : ℝ)*(major1) + (146793155406613/6250000000000 : ℝ)*(major2) + (3262405878502601/100000000000000 : ℝ)*(sp0) + (3262401517736339/100000000000000 : ℝ)*(sp1) + (815597180032643/25000000000000 : ℝ)*(sp2) + (353840579500169/25000000000000 : ℝ)*(sp3) + (2180383131/50000000000000 : ℝ)*(sp5) + (17158372029/100000000000000 : ℝ)*(sp6) + (950557671/5000000000000 : ℝ)*(sp11) + (88461333072131/6250000000000 : ℝ)*(f.failure) + (3262405878502601/100000000000000 : ℝ)*(f.sum) + (36649746812681/22255000000000000000000000000 : ℝ)*base66 + (39586481322509891/34773437500000000000000000000000 : ℝ)*base67 + (55460560965916141/34773437500000000000000000000000 : ℝ)*base69 + (490950814240847907/69546875000000000000000000000000 : ℝ)*base71 + (3059791429279/1390937500000000000000000000 : ℝ)*base73 + (216452223757410407/69546875000000000000000000000000 : ℝ)*base75 + (58922613351409117/17386718750000000000000000000000 : ℝ)*base78 + (350891573072160407/69546875000000000000000000000000 : ℝ)*base79 + (54160222881829/22255000000000000000000000000 : ℝ)*base81 + (2834953/312500000000000000000 : ℝ)*base90 + (2834953/312500000000000000000 : ℝ)*base92 + (2834953/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5041/6250 : ℝ) ≤ (28047804877390967541320108830647/34773437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3066857/20000000000000 : ℝ)*(upper0) + (26229579/100000000000000 : ℝ)*(lower3) + (1260861/10000000000000 : ℝ)*(upper4) + (317326769553481/12500000000000 : ℝ)*(major0) + (317326769553481/12500000000000 : ℝ)*(major1) + (317326769553481/12500000000000 : ℝ)*(major2) + (7618703813/100000000000000 : ℝ)*(sp1) + (1348644021/100000000000000 : ℝ)*(sp2) + (2204738243/100000000000000 : ℝ)*(sp3) + (1316927759/100000000000000 : ℝ)*(sp4) + (1760253270117337/50000000000000 : ℝ)*(sp8) + (176025011922931/5000000000000 : ℝ)*(sp9) + (880126627129603/25000000000000 : ℝ)*(sp10) + (1529832015470051/100000000000000 : ℝ)*(sp11) + (764917110104147/50000000000000 : ℝ)*(f.failure) + (55007935268163/1562500000000 : ℝ)*(f.sum) + (53773497158309/22255000000000000000000000000 : ℝ)*base65 + (801672364080840759/139093750000000000000000000000000 : ℝ)*base67 + (806393801972559509/139093750000000000000000000000000 : ℝ)*base69 + (816405883319872009/139093750000000000000000000000000 : ℝ)*base71 + (6390467174417/695468750000000000000000000 : ℝ)*base73 + (1754327457859872009/139093750000000000000000000000000 : ℝ)*base75 + (405351151407434509/139093750000000000000000000000000 : ℝ)*base77 + (2318088997514747009/139093750000000000000000000000000 : ℝ)*base79 + (24835123875611/22255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (28727161/2500000000000000000000 : ℝ)*base90 + (28727161/2500000000000000000000 : ℝ)*base92 + (28727161/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-17241/20000 : ℝ) ≤ (-29975568309596678946563107401927/34773437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (85294819/100000000000000 : ℝ)*(upper1) + (31146181/100000000000000 : ℝ)*(upper3) + (41210923/100000000000000 : ℝ)*(upper5) + (322308034906921/12500000000000 : ℝ)*(major0) + (322308034906921/12500000000000 : ℝ)*(major1) + (322308034906921/12500000000000 : ℝ)*(major2) + (602673889/100000000000000 : ℝ)*(sp4) + (23826348973/50000000000000 : ℝ)*(sp5) + (103604856573/100000000000000 : ℝ)*(sp6) + (9466165799/50000000000000 : ℝ)*(sp7) + (72636263775671/2000000000000 : ℝ)*(sp12) + (1815883069379747/50000000000000 : ℝ)*(sp13) + (3631710186600867/100000000000000 : ℝ)*(sp14) + (194228749676117/12500000000000 : ℝ)*(sp15) + (776924464870267/50000000000000 : ℝ)*(f.failure) + (22698836196609/625000000000 : ℝ)*(f.sum) + (18122072505729/5563750000000000000000000000 : ℝ)*base66 + (921610759274425081/139093750000000000000000000000000 : ℝ)*base68 + (35745716975237581/139093750000000000000000000000000 : ℝ)*base70 + (647142549926050081/139093750000000000000000000000000 : ℝ)*base72 + (51447501267183/11127500000000000000000000000 : ℝ)*base74 + (7489912208409112581/139093750000000000000000000000000 : ℝ)*base76 + (646765418226081331/139093750000000000000000000000000 : ℝ)*base78 + (1409419791898893831/139093750000000000000000000000000 : ℝ)*base80 + (50060206760729/22255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (27243279/2500000000000000000000 : ℝ)*base89 + (27243279/2500000000000000000000 : ℝ)*base91 + (27243279/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1544_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12757/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58779/100000 : ℝ) else (5041/6250 : ℝ) ≤ X j i ∧ X j i ≤ (17241/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1544_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1544_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12757/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58779/100000 : ℝ) else (5041/6250 : ℝ) ≤ X j i ∧ X j i ≤ (17241/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1544_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1544_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12757/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58779/100000 : ℝ) else (5041/6250 : ℝ) ≤ X j i ∧ X j i ≤ (17241/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1544_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
