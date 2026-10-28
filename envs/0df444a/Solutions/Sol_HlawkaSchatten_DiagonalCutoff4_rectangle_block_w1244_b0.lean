-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1244_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:14.045341+00:00
-- url     : https://prove2.me/submissions/ad1ceb05-96cf-477a-b6ba-3cd984711e9a

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
theorem support_rectangle_w1244_s0_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-92997157/500000000 : ℝ)*x 0 + (6031054561/10000000000 : ℝ)*x 1 + (599154431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92997157/500000000 : ℝ)^8437 ≤ (10847685723059/100000000000000 : ℝ)^6389 := by
    have hnat : (92997157 : ℕ)^8437*100000000000000^6389 ≤ 10847685723059^6389*500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92997157 500000000 10847685723059 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6031054561/10000000000 : ℝ)^8437 ≤ (51285914986069/100000000000000 : ℝ)^6389 := by
    have hnat : (6031054561 : ℕ)^8437*100000000000000^6389 ≤ 51285914986069^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6031054561 10000000000 51285914986069 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599154431/1250000000 : ℝ)^8437 ≤ (18933199633477/50000000000000 : ℝ)^6389 := by
    have hnat : (599154431 : ℕ)^8437*50000000000000^6389 ≤ 18933199633477^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599154431 1250000000 18933199633477 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92997157/500000000 : ℝ), (6031054561/10000000000 : ℝ), (599154431/1250000000 : ℝ)] ![(10847685723059/100000000000000 : ℝ), (51285914986069/100000000000000 : ℝ), (18933199633477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92997157/500000000 : ℝ)|^8437 ≤ (10847685723059/100000000000000 : ℝ)^6389
        have hw : |(-92997157/500000000 : ℝ)|=(92997157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6031054561/10000000000 : ℝ)|^8437 ≤ (51285914986069/100000000000000 : ℝ)^6389
        have hw : |(6031054561/10000000000 : ℝ)|=(6031054561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599154431/1250000000 : ℝ)|^8437 ≤ (18933199633477/50000000000000 : ℝ)^6389
        have hw : |(599154431/1250000000 : ℝ)|=(599154431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s0_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755523409/5000000000 : ℝ)*x 0 + (-513504073/2000000000 : ℝ)*x 1 + (4793235393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755523409/5000000000 : ℝ)^8437 ≤ (45528825432713/100000000000000 : ℝ)^6389 := by
    have hnat : (2755523409 : ℕ)^8437*100000000000000^6389 ≤ 45528825432713^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755523409 5000000000 45528825432713 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513504073/2000000000 : ℝ)^8437 ≤ (166047758563/1000000000000 : ℝ)^6389 := by
    have hnat : (513504073 : ℕ)^8437*1000000000000^6389 ≤ 166047758563^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513504073 2000000000 166047758563 1000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4793235393/10000000000 : ℝ)^8437 ≤ (37866398693177/100000000000000 : ℝ)^6389 := by
    have hnat : (4793235393 : ℕ)^8437*100000000000000^6389 ≤ 37866398693177^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793235393 10000000000 37866398693177 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755523409/5000000000 : ℝ), (-513504073/2000000000 : ℝ), (4793235393/10000000000 : ℝ)] ![(45528825432713/100000000000000 : ℝ), (166047758563/1000000000000 : ℝ), (37866398693177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755523409/5000000000 : ℝ)|^8437 ≤ (45528825432713/100000000000000 : ℝ)^6389
        have hw : |(2755523409/5000000000 : ℝ)|=(2755523409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513504073/2000000000 : ℝ)|^8437 ≤ (166047758563/1000000000000 : ℝ)^6389
        have hw : |(-513504073/2000000000 : ℝ)|=(513504073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4793235393/10000000000 : ℝ)|^8437 ≤ (37866398693177/100000000000000 : ℝ)^6389
        have hw : |(4793235393/10000000000 : ℝ)|=(4793235393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s0_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755523369/5000000000 : ℝ)*x 0 + (1198308869/2500000000 : ℝ)*x 1 + (-2567520367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755523369/5000000000 : ℝ)^8437 ≤ (45528824559947/100000000000000 : ℝ)^6389 := by
    have hnat : (2755523369 : ℕ)^8437*100000000000000^6389 ≤ 45528824559947^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755523369 5000000000 45528824559947 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198308869/2500000000 : ℝ)^8437 ≤ (18933199779529/50000000000000 : ℝ)^6389 := by
    have hnat : (1198308869 : ℕ)^8437*50000000000000^6389 ≤ 18933199779529^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198308869 2500000000 18933199779529 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567520367/10000000000 : ℝ)^8437 ≤ (830238793669/5000000000000 : ℝ)^6389 := by
    have hnat : (2567520367 : ℕ)^8437*5000000000000^6389 ≤ 830238793669^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567520367 10000000000 830238793669 5000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755523369/5000000000 : ℝ), (1198308869/2500000000 : ℝ), (-2567520367/10000000000 : ℝ)] ![(45528824559947/100000000000000 : ℝ), (18933199779529/50000000000000 : ℝ), (830238793669/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755523369/5000000000 : ℝ)|^8437 ≤ (45528824559947/100000000000000 : ℝ)^6389
        have hw : |(2755523369/5000000000 : ℝ)|=(2755523369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1198308869/2500000000 : ℝ)|^8437 ≤ (18933199779529/50000000000000 : ℝ)^6389
        have hw : |(1198308869/2500000000 : ℝ)|=(1198308869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2567520367/10000000000 : ℝ)|^8437 ≤ (830238793669/5000000000000 : ℝ)^6389
        have hw : |(-2567520367/10000000000 : ℝ)|=(2567520367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s0_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4192864529/10000000000 : ℝ)*x 0 + (1558408073/5000000000 : ℝ)*x 1 + (351799321/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192864529/10000000000 : ℝ)^8437 ≤ (7933162103323/25000000000000 : ℝ)^6389 := by
    have hnat : (4192864529 : ℕ)^8437*25000000000000^6389 ≤ 7933162103323^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192864529 10000000000 7933162103323 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558408073/5000000000 : ℝ)^8437 ≤ (5362407756369/25000000000000 : ℝ)^6389 := by
    have hnat : (1558408073 : ℕ)^8437*25000000000000^6389 ≤ 5362407756369^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558408073 5000000000 5362407756369 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351799321/625000000 : ℝ)^8437 ≤ (11704430133767/25000000000000 : ℝ)^6389 := by
    have hnat : (351799321 : ℕ)^8437*25000000000000^6389 ≤ 11704430133767^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351799321 625000000 11704430133767 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192864529/10000000000 : ℝ), (1558408073/5000000000 : ℝ), (351799321/625000000 : ℝ)] ![(7933162103323/25000000000000 : ℝ), (5362407756369/25000000000000 : ℝ), (11704430133767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192864529/10000000000 : ℝ)|^8437 ≤ (7933162103323/25000000000000 : ℝ)^6389
        have hw : |(4192864529/10000000000 : ℝ)|=(4192864529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1558408073/5000000000 : ℝ)|^8437 ≤ (5362407756369/25000000000000 : ℝ)^6389
        have hw : |(1558408073/5000000000 : ℝ)|=(1558408073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(351799321/625000000 : ℝ)|^8437 ≤ (11704430133767/25000000000000 : ℝ)^6389
        have hw : |(351799321/625000000 : ℝ)|=(351799321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s0_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-932397483/5000000000 : ℝ)*x 0 + (150784709/312500000 : ℝ)*x 1 + (5998052609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932397483/5000000000 : ℝ)^8437 ≤ (1360633645093/12500000000000 : ℝ)^6389 := by
    have hnat : (932397483 : ℕ)^8437*12500000000000^6389 ≤ 1360633645093^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932397483 5000000000 1360633645093 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150784709/312500000 : ℝ)^8437 ≤ (19099642743959/50000000000000 : ℝ)^6389 := by
    have hnat : (150784709 : ℕ)^8437*50000000000000^6389 ≤ 19099642743959^6389*312500000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150784709 312500000 19099642743959 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5998052609/10000000000 : ℝ)^8437 ≤ (1272891133501/2500000000000 : ℝ)^6389 := by
    have hnat : (5998052609 : ℕ)^8437*2500000000000^6389 ≤ 1272891133501^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998052609 10000000000 1272891133501 2500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-932397483/5000000000 : ℝ), (150784709/312500000 : ℝ), (5998052609/10000000000 : ℝ)] ![(1360633645093/12500000000000 : ℝ), (19099642743959/50000000000000 : ℝ), (1272891133501/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-932397483/5000000000 : ℝ)|^8437 ≤ (1360633645093/12500000000000 : ℝ)^6389
        have hw : |(-932397483/5000000000 : ℝ)|=(932397483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150784709/312500000 : ℝ)|^8437 ≤ (19099642743959/50000000000000 : ℝ)^6389
        have hw : |(150784709/312500000 : ℝ)|=(150784709/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5998052609/10000000000 : ℝ)|^8437 ≤ (1272891133501/2500000000000 : ℝ)^6389
        have hw : |(5998052609/10000000000 : ℝ)|=(5998052609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s0_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587122621/5000000000 : ℝ)*x 0 + (-1362700963/10000000000 : ℝ)*x 1 + (5998054909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587122621/5000000000 : ℝ)^8437 ≤ (4189096807303/10000000000000 : ℝ)^6389 := by
    have hnat : (2587122621 : ℕ)^8437*10000000000000^6389 ≤ 4189096807303^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587122621 5000000000 4189096807303 10000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362700963/10000000000 : ℝ)^8437 ≤ (1798340198591/25000000000000 : ℝ)^6389 := by
    have hnat : (1362700963 : ℕ)^8437*25000000000000^6389 ≤ 1798340198591^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362700963 10000000000 1798340198591 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5998054909/10000000000 : ℝ)^8437 ≤ (636445889031/1250000000000 : ℝ)^6389 := by
    have hnat : (5998054909 : ℕ)^8437*1250000000000^6389 ≤ 636445889031^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998054909 10000000000 636445889031 1250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587122621/5000000000 : ℝ), (-1362700963/10000000000 : ℝ), (5998054909/10000000000 : ℝ)] ![(4189096807303/10000000000000 : ℝ), (1798340198591/25000000000000 : ℝ), (636445889031/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587122621/5000000000 : ℝ)|^8437 ≤ (4189096807303/10000000000000 : ℝ)^6389
        have hw : |(2587122621/5000000000 : ℝ)|=(2587122621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1362700963/10000000000 : ℝ)|^8437 ≤ (1798340198591/25000000000000 : ℝ)^6389
        have hw : |(-1362700963/10000000000 : ℝ)|=(1362700963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5998054909/10000000000 : ℝ)|^8437 ≤ (636445889031/1250000000000 : ℝ)^6389
        have hw : |(5998054909/10000000000 : ℝ)|=(5998054909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s0_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034849233/2000000000 : ℝ)*x 0 + (5998053059/10000000000 : ℝ)*x 1 + (-1362702521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034849233/2000000000 : ℝ)^8437 ≤ (8378195588211/20000000000000 : ℝ)^6389 := by
    have hnat : (1034849233 : ℕ)^8437*20000000000000^6389 ≤ 8378195588211^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034849233 2000000000 8378195588211 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5998053059/10000000000 : ℝ)^8437 ≤ (50915650384431/100000000000000 : ℝ)^6389 := by
    have hnat : (5998053059 : ℕ)^8437*100000000000000^6389 ≤ 50915650384431^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998053059 10000000000 50915650384431 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362702521/10000000000 : ℝ)^8437 ≤ (899171456871/12500000000000 : ℝ)^6389 := by
    have hnat : (1362702521 : ℕ)^8437*12500000000000^6389 ≤ 899171456871^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362702521 10000000000 899171456871 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034849233/2000000000 : ℝ), (5998053059/10000000000 : ℝ), (-1362702521/10000000000 : ℝ)] ![(8378195588211/20000000000000 : ℝ), (50915650384431/100000000000000 : ℝ), (899171456871/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034849233/2000000000 : ℝ)|^8437 ≤ (8378195588211/20000000000000 : ℝ)^6389
        have hw : |(1034849233/2000000000 : ℝ)|=(1034849233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5998053059/10000000000 : ℝ)|^8437 ≤ (50915650384431/100000000000000 : ℝ)^6389
        have hw : |(5998053059/10000000000 : ℝ)|=(5998053059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1362702521/10000000000 : ℝ)|^8437 ≤ (899171456871/12500000000000 : ℝ)^6389
        have hw : |(-1362702521/10000000000 : ℝ)|=(1362702521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s0_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1050677937/2500000000 : ℝ)*x 0 + (2782054147/5000000000 : ℝ)*x 1 + (3183782919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050677937/2500000000 : ℝ)^8437 ≤ (31831101107511/100000000000000 : ℝ)^6389 := by
    have hnat : (1050677937 : ℕ)^8437*100000000000000^6389 ≤ 31831101107511^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050677937 2500000000 31831101107511 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2782054147/5000000000 : ℝ)^8437 ≤ (46108594514547/100000000000000 : ℝ)^6389 := by
    have hnat : (2782054147 : ℕ)^8437*100000000000000^6389 ≤ 46108594514547^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782054147 5000000000 46108594514547 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183782919/10000000000 : ℝ)^8437 ≤ (11030152183577/50000000000000 : ℝ)^6389 := by
    have hnat : (3183782919 : ℕ)^8437*50000000000000^6389 ≤ 11030152183577^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183782919 10000000000 11030152183577 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050677937/2500000000 : ℝ), (2782054147/5000000000 : ℝ), (3183782919/10000000000 : ℝ)] ![(31831101107511/100000000000000 : ℝ), (46108594514547/100000000000000 : ℝ), (11030152183577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050677937/2500000000 : ℝ)|^8437 ≤ (31831101107511/100000000000000 : ℝ)^6389
        have hw : |(1050677937/2500000000 : ℝ)|=(1050677937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2782054147/5000000000 : ℝ)|^8437 ≤ (46108594514547/100000000000000 : ℝ)^6389
        have hw : |(2782054147/5000000000 : ℝ)|=(2782054147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183782919/10000000000 : ℝ)|^8437 ≤ (11030152183577/50000000000000 : ℝ)^6389
        have hw : |(3183782919/10000000000 : ℝ)|=(3183782919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (413/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27429/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2109/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2109 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2109*1^512 ≤ 0^512*1^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2109/512 : ℝ) ≤ (71726421770657449/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2109 ≤ (71726421770657449/3125000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2109*3125000000000000000^512 ≤ 71726421770657449^512*5^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 71726421770657449 3125000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (71726421770657449/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2109 := by
      have hnat : (1 : ℕ)^512*1^2109 ≤ 1^2109*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (3196726421770657449/3125000000000000000 : ℝ) ≤ (2011048729117441/2000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (3196726421770657449/3125000000000000000 : ℝ)^512 ≤ (2011048729117441/2000000000000000 : ℝ)^2109 := by
      have hnat : (3196726421770657449 : ℕ)^512*2000000000000000^2109 ≤ 2011048729117441^2109*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3196726421770657449 3125000000000000000 2011048729117441 2000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011048729117441/2000000000000000 : ℝ)) (X := (3196726421770657449/3125000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1634226421770657449/1562500000000000000 : ℝ) ≤ (1011048729117441/1000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (1634226421770657449/1562500000000000000 : ℝ)^512 ≤ (1011048729117441/1000000000000000 : ℝ)^2109 := by
      have hnat : (1634226421770657449 : ℕ)^512*1000000000000000^2109 ≤ 1011048729117441^2109*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1634226421770657449 1562500000000000000 1011048729117441 1000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011048729117441/1000000000000000 : ℝ)) (X := (1634226421770657449/1562500000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11048729117441/800000000000000 : ℝ)*(0 : ℝ))^(2109/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(11048729117441/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71726421770657449/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11048729117441/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (1 : ℝ)+(11048729117441/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011048729117441/2000000000000000 : ℝ) by norm_num, show 1+(71726421770657449/3125000000000000000 : ℝ)+(0 : ℝ)=(3196726421770657449/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71726421770657449/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11048729117441/800000000000000 : ℝ)*(2/5 : ℝ))^(2109/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(11048729117441/800000000000000 : ℝ)*(2/5 : ℝ)=(1011048729117441/1000000000000000 : ℝ) by norm_num, show 1+2*(71726421770657449/3125000000000000000 : ℝ)=(1634226421770657449/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11048729117441/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11048729117441/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11048729117441/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11048729117441/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11048729117441/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11048729117441/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-92997157/500000000 : ℝ)*X 0 0+(6031054561/10000000000 : ℝ)*X 0 1+(599154431/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755523409/5000000000 : ℝ)*X 1 0+(-513504073/2000000000 : ℝ)*X 1 1+(4793235393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2755523369/5000000000 : ℝ)*X 2 0+(1198308869/2500000000 : ℝ)*X 2 1+(-2567520367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4192864529/10000000000 : ℝ)*X 0 0+(1558408073/5000000000 : ℝ)*X 0 1+(351799321/625000000 : ℝ)*X 0 2+(4192864529/10000000000 : ℝ)*X 1 0+(1558408073/5000000000 : ℝ)*X 1 1+(351799321/625000000 : ℝ)*X 1 2+(4192864529/10000000000 : ℝ)*X 2 0+(1558408073/5000000000 : ℝ)*X 2 1+(351799321/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-932397483/5000000000 : ℝ)*X 0 0+(150784709/312500000 : ℝ)*X 0 1+(5998052609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587122621/5000000000 : ℝ)*X 1 0+(-1362700963/10000000000 : ℝ)*X 1 1+(5998054909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034849233/2000000000 : ℝ)*X 2 0+(5998053059/10000000000 : ℝ)*X 2 1+(-1362702521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050677937/2500000000 : ℝ)*X 0 0+(2782054147/5000000000 : ℝ)*X 0 1+(3183782919/10000000000 : ℝ)*X 0 2+(1050677937/2500000000 : ℝ)*X 1 0+(2782054147/5000000000 : ℝ)*X 1 1+(3183782919/10000000000 : ℝ)*X 1 2+(1050677937/2500000000 : ℝ)*X 2 0+(2782054147/5000000000 : ℝ)*X 2 1+(3183782919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50470545277400623843959/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31775879/50000000000000 : ℝ)*(base1) + (1231916589/100000000000000 : ℝ)*(base19) + (28470069/2500000000000 : ℝ)*(base23) + (81386429/100000000000000 : ℝ)*(base24) + (2755771/1000000000000 : ℝ)*(upper3) + (301494101524867/50000000000000 : ℝ)*(major0) + (301494101524867/50000000000000 : ℝ)*(major1) + (301494101524867/50000000000000 : ℝ)*(major2) + (100984582411519/12500000000000 : ℝ)*(sp0) + (161575622138873/20000000000000 : ℝ)*(sp1) + (201969530605441/25000000000000 : ℝ)*(sp2) + (398094706152659/100000000000000 : ℝ)*(sp3) + (2746870559/100000000000000 : ℝ)*(sp4) + (1062774471/50000000000000 : ℝ)*(sp7) + (398096895253359/100000000000000 : ℝ)*(f.failure) + (403939671305477/50000000000000 : ℝ)*(f.sum) + (2472025845347/20000000000000000000000000000 : ℝ)*base65 + (121753343865347/40000000000000000000000000000 : ℝ)*base67 + (154034150945347/40000000000000000000000000000 : ℝ)*base69 + (28030126974653/40000000000000000000000000000 : ℝ)*base72 + (27642946165347/20000000000000000000000000000 : ℝ)*base73 + (148918565774653/40000000000000000000000000000 : ℝ)*base76 + (166024862545347/40000000000000000000000000000 : ℝ)*base77 + (77562951865347/40000000000000000000000000000 : ℝ)*base79 + (7794113774653/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (7248791/5000000000000000000000 : ℝ)*base89 + (7248791/5000000000000000000000 : ℝ)*base91 + (7248791/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75369228354724690573797/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33553697/20000000000000 : ℝ)*(base1) + (1817265273/100000000000000 : ℝ)*(base19) + (490515309/25000000000000 : ℝ)*(base23) + (184683283/50000000000000 : ℝ)*(upper3) + (11905471/20000000000000 : ℝ)*(upper5) + (636333496691561/100000000000000 : ℝ)*(major0) + (636333496691561/100000000000000 : ℝ)*(major1) + (636333496691561/100000000000000 : ℝ)*(major2) + (1881411511/50000000000000 : ℝ)*(sp1) + (3650908389/100000000000000 : ℝ)*(sp2) + (426277612990879/50000000000000 : ℝ)*(sp4) + (426274739062489/50000000000000 : ℝ)*(sp5) + (3330271270483/390625000000 : ℝ)*(sp6) + (84022303234119/20000000000000 : ℝ)*(sp7) + (10502792098477/2500000000000 : ℝ)*(f.failure) + (852555058213273/100000000000000 : ℝ)*(f.sum) + (22164129335401/40000000000000000000000000000 : ℝ)*base65 + (330081367895401/80000000000000000000000000000 : ℝ)*base67 + (631511048455401/80000000000000000000000000000 : ℝ)*base69 + (362921024055401/80000000000000000000000000000 : ℝ)*base71 + (60843800824599/40000000000000000000000000000 : ℝ)*base74 + (559852806375401/80000000000000000000000000000 : ℝ)*base75 + (482777317655401/80000000000000000000000000000 : ℝ)*base77 + (342185536535401/80000000000000000000000000000 : ℝ)*base79 + (86118065255401/40000000000000000000000000000 : ℝ)*base81 + (1002027/125000000000000000000 : ℝ)*base90 + (1002027/125000000000000000000 : ℝ)*base92 + (1002027/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1244_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27429/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1244_s1_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-51430131/250000000 : ℝ)*x 0 + (5675111459/10000000000 : ℝ)*x 1 + (5022908609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51430131/250000000 : ℝ)^8437 ≤ (12392191419739/100000000000000 : ℝ)^6389 := by
    have hnat : (51430131 : ℕ)^8437*100000000000000^6389 ≤ 12392191419739^6389*250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51430131 250000000 12392191419739 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5675111459/10000000000 : ℝ)^8437 ≤ (47327182971357/100000000000000 : ℝ)^6389 := by
    have hnat : (5675111459 : ℕ)^8437*100000000000000^6389 ≤ 47327182971357^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675111459 10000000000 47327182971357 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5022908609/10000000000 : ℝ)^8437 ≤ (20140312799107/50000000000000 : ℝ)^6389 := by
    have hnat : (5022908609 : ℕ)^8437*50000000000000^6389 ≤ 20140312799107^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022908609 10000000000 20140312799107 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51430131/250000000 : ℝ), (5675111459/10000000000 : ℝ), (5022908609/10000000000 : ℝ)] ![(12392191419739/100000000000000 : ℝ), (47327182971357/100000000000000 : ℝ), (20140312799107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51430131/250000000 : ℝ)|^8437 ≤ (12392191419739/100000000000000 : ℝ)^6389
        have hw : |(-51430131/250000000 : ℝ)|=(51430131/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5675111459/10000000000 : ℝ)|^8437 ≤ (47327182971357/100000000000000 : ℝ)^6389
        have hw : |(5675111459/10000000000 : ℝ)|=(5675111459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5022908609/10000000000 : ℝ)|^8437 ≤ (20140312799107/50000000000000 : ℝ)^6389
        have hw : |(5022908609/10000000000 : ℝ)|=(5022908609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706775871/5000000000 : ℝ)*x 0 + (-2407398191/10000000000 : ℝ)*x 1 + (2511454403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706775871/5000000000 : ℝ)^8437 ≤ (11117056095731/25000000000000 : ℝ)^6389 := by
    have hnat : (2706775871 : ℕ)^8437*25000000000000^6389 ≤ 11117056095731^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706775871 5000000000 11117056095731 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2407398191/10000000000 : ℝ)^8437 ≤ (3050229582807/20000000000000 : ℝ)^6389 := by
    have hnat : (2407398191 : ℕ)^8437*20000000000000^6389 ≤ 3050229582807^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2407398191 10000000000 3050229582807 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511454403/5000000000 : ℝ)^8437 ≤ (10070156921111/25000000000000 : ℝ)^6389 := by
    have hnat : (2511454403 : ℕ)^8437*25000000000000^6389 ≤ 10070156921111^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511454403 5000000000 10070156921111 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706775871/5000000000 : ℝ), (-2407398191/10000000000 : ℝ), (2511454403/5000000000 : ℝ)] ![(11117056095731/25000000000000 : ℝ), (3050229582807/20000000000000 : ℝ), (10070156921111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706775871/5000000000 : ℝ)|^8437 ≤ (11117056095731/25000000000000 : ℝ)^6389
        have hw : |(2706775871/5000000000 : ℝ)|=(2706775871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2407398191/10000000000 : ℝ)|^8437 ≤ (3050229582807/20000000000000 : ℝ)^6389
        have hw : |(-2407398191/10000000000 : ℝ)|=(2407398191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2511454403/5000000000 : ℝ)|^8437 ≤ (10070156921111/25000000000000 : ℝ)^6389
        have hw : |(2511454403/5000000000 : ℝ)|=(2511454403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (216542077/400000000 : ℝ)*x 0 + (1255727169/2500000000 : ℝ)*x 1 + (-1203699059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216542077/400000000 : ℝ)^8437 ≤ (8893645273597/20000000000000 : ℝ)^6389 := by
    have hnat : (216542077 : ℕ)^8437*20000000000000^6389 ≤ 8893645273597^6389*400000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216542077 400000000 8893645273597 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255727169/2500000000 : ℝ)^8437 ≤ (1258769572117/3125000000000 : ℝ)^6389 := by
    have hnat : (1255727169 : ℕ)^8437*3125000000000^6389 ≤ 1258769572117^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255727169 2500000000 1258769572117 3125000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203699059/5000000000 : ℝ)^8437 ≤ (15251147303329/100000000000000 : ℝ)^6389 := by
    have hnat : (1203699059 : ℕ)^8437*100000000000000^6389 ≤ 15251147303329^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203699059 5000000000 15251147303329 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216542077/400000000 : ℝ), (1255727169/2500000000 : ℝ), (-1203699059/5000000000 : ℝ)] ![(8893645273597/20000000000000 : ℝ), (1258769572117/3125000000000 : ℝ), (15251147303329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216542077/400000000 : ℝ)|^8437 ≤ (8893645273597/20000000000000 : ℝ)^6389
        have hw : |(216542077/400000000 : ℝ)|=(216542077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255727169/2500000000 : ℝ)|^8437 ≤ (1258769572117/3125000000000 : ℝ)^6389
        have hw : |(1255727169/2500000000 : ℝ)|=(1255727169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1203699059/5000000000 : ℝ)|^8437 ≤ (15251147303329/100000000000000 : ℝ)^6389
        have hw : |(-1203699059/5000000000 : ℝ)|=(1203699059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (861736033/2000000000 : ℝ)*x 0 + (3695794859/10000000000 : ℝ)*x 1 + (5019345813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861736033/2000000000 : ℝ)^8437 ≤ (32895232697929/100000000000000 : ℝ)^6389 := by
    have hnat : (861736033 : ℕ)^8437*100000000000000^6389 ≤ 32895232697929^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861736033 2000000000 32895232697929 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3695794859/10000000000 : ℝ)^8437 ≤ (13430933708687/50000000000000 : ℝ)^6389 := by
    have hnat : (3695794859 : ℕ)^8437*50000000000000^6389 ≤ 13430933708687^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3695794859 10000000000 13430933708687 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5019345813/10000000000 : ℝ)^8437 ≤ (40242899867171/100000000000000 : ℝ)^6389 := by
    have hnat : (5019345813 : ℕ)^8437*100000000000000^6389 ≤ 40242899867171^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019345813 10000000000 40242899867171 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861736033/2000000000 : ℝ), (3695794859/10000000000 : ℝ), (5019345813/10000000000 : ℝ)] ![(32895232697929/100000000000000 : ℝ), (13430933708687/50000000000000 : ℝ), (40242899867171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861736033/2000000000 : ℝ)|^8437 ≤ (32895232697929/100000000000000 : ℝ)^6389
        have hw : |(861736033/2000000000 : ℝ)|=(861736033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3695794859/10000000000 : ℝ)|^8437 ≤ (13430933708687/50000000000000 : ℝ)^6389
        have hw : |(3695794859/10000000000 : ℝ)|=(3695794859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5019345813/10000000000 : ℝ)|^8437 ≤ (40242899867171/100000000000000 : ℝ)^6389
        have hw : |(5019345813/10000000000 : ℝ)|=(5019345813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-257235311/1250000000 : ℝ)*x 0 + (1257868161/2500000000 : ℝ)*x 1 + (2833191233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257235311/1250000000 : ℝ)^8437 ≤ (247951580631/2000000000000 : ℝ)^6389 := by
    have hnat : (257235311 : ℕ)^8437*2000000000000^6389 ≤ 247951580631^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257235311 1250000000 247951580631 2000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257868161/2500000000 : ℝ)^8437 ≤ (2523208970649/6250000000000 : ℝ)^6389 := by
    have hnat : (1257868161 : ℕ)^8437*6250000000000^6389 ≤ 2523208970649^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257868161 2500000000 2523208970649 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2833191233/5000000000 : ℝ)^8437 ≤ (23615538712529/50000000000000 : ℝ)^6389 := by
    have hnat : (2833191233 : ℕ)^8437*50000000000000^6389 ≤ 23615538712529^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833191233 5000000000 23615538712529 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257235311/1250000000 : ℝ), (1257868161/2500000000 : ℝ), (2833191233/5000000000 : ℝ)] ![(247951580631/2000000000000 : ℝ), (2523208970649/6250000000000 : ℝ), (23615538712529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257235311/1250000000 : ℝ)|^8437 ≤ (247951580631/2000000000000 : ℝ)^6389
        have hw : |(-257235311/1250000000 : ℝ)|=(257235311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1257868161/2500000000 : ℝ)|^8437 ≤ (2523208970649/6250000000000 : ℝ)^6389
        have hw : |(1257868161/2500000000 : ℝ)|=(1257868161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2833191233/5000000000 : ℝ)|^8437 ≤ (23615538712529/50000000000000 : ℝ)^6389
        have hw : |(2833191233/5000000000 : ℝ)|=(2833191233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327844387/625000000 : ℝ)*x 0 + (-881959791/5000000000 : ℝ)*x 1 + (354149147/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327844387/625000000 : ℝ)^8437 ≤ (42654556266713/100000000000000 : ℝ)^6389 := by
    have hnat : (327844387 : ℕ)^8437*100000000000000^6389 ≤ 42654556266713^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327844387 625000000 42654556266713 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881959791/5000000000 : ℝ)^8437 ≤ (10114323529779/100000000000000 : ℝ)^6389 := by
    have hnat : (881959791 : ℕ)^8437*100000000000000^6389 ≤ 10114323529779^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881959791 5000000000 10114323529779 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (354149147/625000000 : ℝ)^8437 ≤ (11807780049767/25000000000000 : ℝ)^6389 := by
    have hnat : (354149147 : ℕ)^8437*25000000000000^6389 ≤ 11807780049767^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354149147 625000000 11807780049767 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327844387/625000000 : ℝ), (-881959791/5000000000 : ℝ), (354149147/625000000 : ℝ)] ![(42654556266713/100000000000000 : ℝ), (10114323529779/100000000000000 : ℝ), (11807780049767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327844387/625000000 : ℝ)|^8437 ≤ (42654556266713/100000000000000 : ℝ)^6389
        have hw : |(327844387/625000000 : ℝ)|=(327844387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-881959791/5000000000 : ℝ)|^8437 ≤ (10114323529779/100000000000000 : ℝ)^6389
        have hw : |(-881959791/5000000000 : ℝ)|=(881959791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(354149147/625000000 : ℝ)|^8437 ≤ (11807780049767/25000000000000 : ℝ)^6389
        have hw : |(354149147/625000000 : ℝ)|=(354149147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5245510139/10000000000 : ℝ)*x 0 + (1416597169/2500000000 : ℝ)*x 1 + (-1763916277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245510139/10000000000 : ℝ)^8437 ≤ (42654555697587/100000000000000 : ℝ)^6389 := by
    have hnat : (5245510139 : ℕ)^8437*100000000000000^6389 ≤ 42654555697587^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245510139 10000000000 42654555697587 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1416597169/2500000000 : ℝ)^8437 ≤ (1889245831193/4000000000000 : ℝ)^6389 := by
    have hnat : (1416597169 : ℕ)^8437*4000000000000^6389 ≤ 1889245831193^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416597169 2500000000 1889245831193 4000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1763916277/10000000000 : ℝ)^8437 ≤ (632143656511/6250000000000 : ℝ)^6389 := by
    have hnat : (1763916277 : ℕ)^8437*6250000000000^6389 ≤ 632143656511^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763916277 10000000000 632143656511 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245510139/10000000000 : ℝ), (1416597169/2500000000 : ℝ), (-1763916277/10000000000 : ℝ)] ![(42654555697587/100000000000000 : ℝ), (1889245831193/4000000000000 : ℝ), (632143656511/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245510139/10000000000 : ℝ)|^8437 ≤ (42654555697587/100000000000000 : ℝ)^6389
        have hw : |(5245510139/10000000000 : ℝ)|=(5245510139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1416597169/2500000000 : ℝ)|^8437 ≤ (1889245831193/4000000000000 : ℝ)^6389
        have hw : |(1416597169/2500000000 : ℝ)|=(1416597169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1763916277/10000000000 : ℝ)|^8437 ≤ (632143656511/6250000000000 : ℝ)^6389
        have hw : |(-1763916277/10000000000 : ℝ)|=(1763916277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4310050033/10000000000 : ℝ)*x 0 + (5001974047/10000000000 : ℝ)*x 1 + (928373599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310050033/10000000000 : ℝ)^8437 ≤ (32909044320923/100000000000000 : ℝ)^6389 := by
    have hnat : (4310050033 : ℕ)^8437*100000000000000^6389 ≤ 32909044320923^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310050033 10000000000 32909044320923 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001974047/10000000000 : ℝ)^8437 ≤ (20029538376457/50000000000000 : ℝ)^6389 := by
    have hnat : (5001974047 : ℕ)^8437*50000000000000^6389 ≤ 20029538376457^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001974047 10000000000 20029538376457 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928373599/2500000000 : ℝ)^8437 ≤ (27031878908481/100000000000000 : ℝ)^6389 := by
    have hnat : (928373599 : ℕ)^8437*100000000000000^6389 ≤ 27031878908481^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928373599 2500000000 27031878908481 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310050033/10000000000 : ℝ), (5001974047/10000000000 : ℝ), (928373599/2500000000 : ℝ)] ![(32909044320923/100000000000000 : ℝ), (20029538376457/50000000000000 : ℝ), (27031878908481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310050033/10000000000 : ℝ)|^8437 ≤ (32909044320923/100000000000000 : ℝ)^6389
        have hw : |(4310050033/10000000000 : ℝ)|=(4310050033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001974047/10000000000 : ℝ)|^8437 ≤ (20029538376457/50000000000000 : ℝ)^6389
        have hw : |(5001974047/10000000000 : ℝ)|=(5001974047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(928373599/2500000000 : ℝ)|^8437 ≤ (27031878908481/100000000000000 : ℝ)^6389
        have hw : |(928373599/2500000000 : ℝ)|=(928373599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_8 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (998367/5000000000 : ℝ)*x 0 + (2486338161/5000000000 : ℝ)*x 1 + (6813430983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998367/5000000000 : ℝ)^8437 ≤ (325330187/25000000000000 : ℝ)^6389 := by
    have hnat : (998367 : ℕ)^8437*25000000000000^6389 ≤ 325330187^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998367 5000000000 325330187 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2486338161/5000000000 : ℝ)^8437 ≤ (39749520113063/100000000000000 : ℝ)^6389 := by
    have hnat : (2486338161 : ℕ)^8437*100000000000000^6389 ≤ 39749520113063^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486338161 5000000000 39749520113063 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6813430983/10000000000 : ℝ)^8437 ≤ (60249178552403/100000000000000 : ℝ)^6389 := by
    have hnat : (6813430983 : ℕ)^8437*100000000000000^6389 ≤ 60249178552403^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6813430983 10000000000 60249178552403 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(998367/5000000000 : ℝ), (2486338161/5000000000 : ℝ), (6813430983/10000000000 : ℝ)] ![(325330187/25000000000000 : ℝ), (39749520113063/100000000000000 : ℝ), (60249178552403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(998367/5000000000 : ℝ)|^8437 ≤ (325330187/25000000000000 : ℝ)^6389
        have hw : |(998367/5000000000 : ℝ)|=(998367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2486338161/5000000000 : ℝ)|^8437 ≤ (39749520113063/100000000000000 : ℝ)^6389
        have hw : |(2486338161/5000000000 : ℝ)|=(2486338161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6813430983/10000000000 : ℝ)|^8437 ≤ (60249178552403/100000000000000 : ℝ)^6389
        have hw : |(6813430983/10000000000 : ℝ)|=(6813430983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_9 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (500389837/5000000000 : ℝ)*x 0 + (-2171896081/5000000000 : ℝ)*x 1 + (6959879239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (500389837/5000000000 : ℝ)^8437 ≤ (1196288800031/25000000000000 : ℝ)^6389 := by
    have hnat : (500389837 : ℕ)^8437*25000000000000^6389 ≤ 1196288800031^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500389837 5000000000 1196288800031 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171896081/5000000000 : ℝ)^8437 ≤ (16624845527263/50000000000000 : ℝ)^6389 := by
    have hnat : (2171896081 : ℕ)^8437*50000000000000^6389 ≤ 16624845527263^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171896081 5000000000 16624845527263 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6959879239/10000000000 : ℝ)^8437 ≤ (61965153728121/100000000000000 : ℝ)^6389 := by
    have hnat : (6959879239 : ℕ)^8437*100000000000000^6389 ≤ 61965153728121^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6959879239 10000000000 61965153728121 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(500389837/5000000000 : ℝ), (-2171896081/5000000000 : ℝ), (6959879239/10000000000 : ℝ)] ![(1196288800031/25000000000000 : ℝ), (16624845527263/50000000000000 : ℝ), (61965153728121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(500389837/5000000000 : ℝ)|^8437 ≤ (1196288800031/25000000000000 : ℝ)^6389
        have hw : |(500389837/5000000000 : ℝ)|=(500389837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2171896081/5000000000 : ℝ)|^8437 ≤ (16624845527263/50000000000000 : ℝ)^6389
        have hw : |(-2171896081/5000000000 : ℝ)|=(2171896081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6959879239/10000000000 : ℝ)|^8437 ≤ (61965153728121/100000000000000 : ℝ)^6389
        have hw : |(6959879239/10000000000 : ℝ)|=(6959879239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_10 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (500391351/5000000000 : ℝ)*x 0 + (3479942613/5000000000 : ℝ)*x 1 + (-4343783307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (500391351/5000000000 : ℝ)^8437 ≤ (4785174319283/100000000000000 : ℝ)^6389 := by
    have hnat : (500391351 : ℕ)^8437*100000000000000^6389 ≤ 4785174319283^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500391351 5000000000 4785174319283 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3479942613/5000000000 : ℝ)^8437 ≤ (30982612059007/50000000000000 : ℝ)^6389 := by
    have hnat : (3479942613 : ℕ)^8437*50000000000000^6389 ≤ 30982612059007^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3479942613 5000000000 30982612059007 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4343783307/10000000000 : ℝ)^8437 ≤ (33249601546463/100000000000000 : ℝ)^6389 := by
    have hnat : (4343783307 : ℕ)^8437*100000000000000^6389 ≤ 33249601546463^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343783307 10000000000 33249601546463 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(500391351/5000000000 : ℝ), (3479942613/5000000000 : ℝ), (-4343783307/10000000000 : ℝ)] ![(4785174319283/100000000000000 : ℝ), (30982612059007/50000000000000 : ℝ), (33249601546463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(500391351/5000000000 : ℝ)|^8437 ≤ (4785174319283/100000000000000 : ℝ)^6389
        have hw : |(500391351/5000000000 : ℝ)|=(500391351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3479942613/5000000000 : ℝ)|^8437 ≤ (30982612059007/50000000000000 : ℝ)^6389
        have hw : |(3479942613/5000000000 : ℝ)|=(3479942613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4343783307/10000000000 : ℝ)|^8437 ≤ (33249601546463/100000000000000 : ℝ)^6389
        have hw : |(-4343783307/10000000000 : ℝ)|=(4343783307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s1_11 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1999404251/10000000000 : ℝ)*x 0 + (2682424789/5000000000 : ℝ)*x 1 + (5381863691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999404251/10000000000 : ℝ)^8437 ≤ (11934483820513/100000000000000 : ℝ)^6389 := by
    have hnat : (1999404251 : ℕ)^8437*100000000000000^6389 ≤ 11934483820513^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999404251 10000000000 11934483820513 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2682424789/5000000000 : ℝ)^8437 ≤ (2746293716801/6250000000000 : ℝ)^6389 := by
    have hnat : (2682424789 : ℕ)^8437*6250000000000^6389 ≤ 2746293716801^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682424789 5000000000 2746293716801 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5381863691/10000000000 : ℝ)^8437 ≤ (22062408348289/50000000000000 : ℝ)^6389 := by
    have hnat : (5381863691 : ℕ)^8437*50000000000000^6389 ≤ 22062408348289^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381863691 10000000000 22062408348289 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1999404251/10000000000 : ℝ), (2682424789/5000000000 : ℝ), (5381863691/10000000000 : ℝ)] ![(11934483820513/100000000000000 : ℝ), (2746293716801/6250000000000 : ℝ), (22062408348289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1999404251/10000000000 : ℝ)|^8437 ≤ (11934483820513/100000000000000 : ℝ)^6389
        have hw : |(1999404251/10000000000 : ℝ)|=(1999404251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2682424789/5000000000 : ℝ)|^8437 ≤ (2746293716801/6250000000000 : ℝ)^6389
        have hw : |(2682424789/5000000000 : ℝ)|=(2682424789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5381863691/10000000000 : ℝ)|^8437 ≤ (22062408348289/50000000000000 : ℝ)^6389
        have hw : |(5381863691/10000000000 : ℝ)|=(5381863691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27429/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6201/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1999/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27429/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (413/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27429/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (413/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27429/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (413/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27429/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (413/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27429/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (413/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27429/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (413/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (413/50000 : ℝ) ^ (2109/512 : ℝ) ≤ (262874155339/100000000000000000000 : ℝ) := by
    have hpowers : (413/50000 : ℝ)^2109 ≤ (262874155339/100000000000000000000 : ℝ)^512 := by
      have hnat : (413 : ℕ)^2109*100000000000000000000^512 ≤ 262874155339^512*50000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 50000 262874155339 100000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/50000 : ℝ)) (X := (262874155339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27429/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (485185578092181411/100000000000000000000 : ℝ) := by
    have hpowers : (27429/100000 : ℝ)^2109 ≤ (485185578092181411/100000000000000000000 : ℝ)^512 := by
      have hnat : (27429 : ℕ)^2109*100000000000000000000^512 ≤ 485185578092181411^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27429 100000 485185578092181411 100000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27429/100000 : ℝ)) (X := (485185578092181411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000262874155339/50000000000000000000 : ℝ) ≤ (1250000001595443/1250000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50000000262874155339/50000000000000000000 : ℝ)^512 ≤ (1250000001595443/1250000000000000 : ℝ)^2109 := by
      have hnat : (50000000262874155339 : ℕ)^512*1250000000000000^2109 ≤ 1250000001595443^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000262874155339 50000000000000000000 1250000001595443 1250000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000001595443/1250000000000000 : ℝ)) (X := (50000000262874155339/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (401940743363865347/400000000000000000 : ℝ) ≤ (2002351447200919/2000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (401940743363865347/400000000000000000 : ℝ)^512 ≤ (2002351447200919/2000000000000000 : ℝ)^2109 := by
      have hnat : (401940743363865347 : ℕ)^512*2000000000000000^2109 ≤ 2002351447200919^2109*400000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401940743363865347 400000000000000000 2002351447200919 2000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002351447200919/2000000000000000 : ℝ)) (X := (401940743363865347/400000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50485185578092181411/50000000000000000000 : ℝ) ≤ (5011757229622823/5000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50485185578092181411/50000000000000000000 : ℝ)^512 ≤ (5011757229622823/5000000000000000 : ℝ)^2109 := by
      have hnat : (50485185578092181411 : ℕ)^512*5000000000000000^2109 ≤ 5011757229622823^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50485185578092181411 50000000000000000000 5011757229622823 5000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011757229622823/5000000000000000 : ℝ)) (X := (50485185578092181411/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(262874155339/100000000000000000000 : ℝ) ≤ ((13300528870337717239/13301500000000000000 : ℝ)+2*(11757223241051/2660300000000000 : ℝ)*(413/50000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (13300528870337717239/13301500000000000000 : ℝ)+2*(11757223241051/2660300000000000 : ℝ)*(413/50000 : ℝ)=(1250000001595443/1250000000000000 : ℝ) by norm_num, show 1+2*(262874155339/100000000000000000000 : ℝ)=(50000000262874155339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(485185578092181411/100000000000000000000 : ℝ)+(262874155339/100000000000000000000 : ℝ) ≤ ((13300528870337717239/13301500000000000000 : ℝ)+(11757223241051/2660300000000000 : ℝ)*((27429/100000 : ℝ)+(413/50000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (13300528870337717239/13301500000000000000 : ℝ)+(11757223241051/2660300000000000 : ℝ)*((27429/100000 : ℝ)+(413/50000 : ℝ))=(2002351447200919/2000000000000000 : ℝ) by norm_num, show 1+(485185578092181411/100000000000000000000 : ℝ)+(262874155339/100000000000000000000 : ℝ)=(401940743363865347/400000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(485185578092181411/100000000000000000000 : ℝ) ≤ ((13300528870337717239/13301500000000000000 : ℝ)+2*(11757223241051/2660300000000000 : ℝ)*(27429/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (13300528870337717239/13301500000000000000 : ℝ)+2*(11757223241051/2660300000000000 : ℝ)*(27429/100000 : ℝ)=(5011757229622823/5000000000000000 : ℝ) by norm_num, show 1+2*(485185578092181411/100000000000000000000 : ℝ)=(50485185578092181411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13300528870337717239/13301500000000000000 : ℝ)*(X 1 0+X 2 0)+(11757223241051/2660300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (413/50000 : ℝ)) (hi := (27429/100000 : ℝ)) (c := (13300528870337717239/13301500000000000000 : ℝ)) (alpha := (11757223241051/2660300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13300528870337717239/13301500000000000000 : ℝ)*(X 0 1+X 2 1)+(11757223241051/2660300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (413/50000 : ℝ)) (hi := (27429/100000 : ℝ)) (c := (13300528870337717239/13301500000000000000 : ℝ)) (alpha := (11757223241051/2660300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13300528870337717239/13301500000000000000 : ℝ)*(X 0 2+X 1 2)+(11757223241051/2660300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (413/50000 : ℝ)) (hi := (27429/100000 : ℝ)) (c := (13300528870337717239/13301500000000000000 : ℝ)) (alpha := (11757223241051/2660300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51430131/250000000 : ℝ)*X 0 0+(5675111459/10000000000 : ℝ)*X 0 1+(5022908609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706775871/5000000000 : ℝ)*X 1 0+(-2407398191/10000000000 : ℝ)*X 1 1+(2511454403/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((216542077/400000000 : ℝ)*X 2 0+(1255727169/2500000000 : ℝ)*X 2 1+(-1203699059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861736033/2000000000 : ℝ)*X 0 0+(3695794859/10000000000 : ℝ)*X 0 1+(5019345813/10000000000 : ℝ)*X 0 2+(861736033/2000000000 : ℝ)*X 1 0+(3695794859/10000000000 : ℝ)*X 1 1+(5019345813/10000000000 : ℝ)*X 1 2+(861736033/2000000000 : ℝ)*X 2 0+(3695794859/10000000000 : ℝ)*X 2 1+(5019345813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-257235311/1250000000 : ℝ)*X 0 0+(1257868161/2500000000 : ℝ)*X 0 1+(2833191233/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((327844387/625000000 : ℝ)*X 1 0+(-881959791/5000000000 : ℝ)*X 1 1+(354149147/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245510139/10000000000 : ℝ)*X 2 0+(1416597169/2500000000 : ℝ)*X 2 1+(-1763916277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310050033/10000000000 : ℝ)*X 0 0+(5001974047/10000000000 : ℝ)*X 0 1+(928373599/2500000000 : ℝ)*X 0 2+(4310050033/10000000000 : ℝ)*X 1 0+(5001974047/10000000000 : ℝ)*X 1 1+(928373599/2500000000 : ℝ)*X 1 2+(4310050033/10000000000 : ℝ)*X 2 0+(5001974047/10000000000 : ℝ)*X 2 1+(928373599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((998367/5000000000 : ℝ)*X 0 0+(2486338161/5000000000 : ℝ)*X 0 1+(6813430983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((500389837/5000000000 : ℝ)*X 1 0+(-2171896081/5000000000 : ℝ)*X 1 1+(6959879239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((500391351/5000000000 : ℝ)*X 2 0+(3479942613/5000000000 : ℝ)*X 2 1+(-4343783307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1999404251/10000000000 : ℝ)*X 0 0+(2682424789/5000000000 : ℝ)*X 0 1+(5381863691/10000000000 : ℝ)*X 0 2+(1999404251/10000000000 : ℝ)*X 1 0+(2682424789/5000000000 : ℝ)*X 1 1+(5381863691/10000000000 : ℝ)*X 1 2+(1999404251/10000000000 : ℝ)*X 2 0+(2682424789/5000000000 : ℝ)*X 2 1+(5381863691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130328881274864030017884891/8987500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1144409333615251/100000000000000 : ℝ)*(major0) + (1144409333615251/100000000000000 : ℝ)*(major1) + (1144409333615251/100000000000000 : ℝ)*(major2) + (766634891736149/50000000000000 : ℝ)*(sp0) + (1533269158192669/100000000000000 : ℝ)*(sp1) + (766634514662987/50000000000000 : ℝ)*(sp2) + (377772031190797/50000000000000 : ℝ)*(sp3) + (1351923429/100000000000000 : ℝ)*(sp5) + (35494709/2500000000000 : ℝ)*(sp6) + (879735537/100000000000000 : ℝ)*(sp7) + (402020899/25000000000000 : ℝ)*(sp8) + (220359949/25000000000000 : ℝ)*(sp9) + (23561039/2500000000000 : ℝ)*(sp10) + (925093283/50000000000000 : ℝ)*(sp11) + (755546792303697/100000000000000 : ℝ)*(f.failure) + (766635695777947/50000000000000 : ℝ)*(f.sum) + (169429812919843/66507500000000000000000000000 : ℝ)*base65 + (5559849460009033011/1330150000000000000000000000000000 : ℝ)*base68 + (4007139697104483011/1330150000000000000000000000000000 : ℝ)*base70 + (1062178956879966989/1330150000000000000000000000000000 : ℝ)*base71 + (223543138448441/133015000000000000000000000000 : ℝ)*base73 + (4047724058051883011/1330150000000000000000000000000000 : ℝ)*base76 + (2073121385746033011/1330150000000000000000000000000000 : ℝ)*base78 + (5101050996156533011/1330150000000000000000000000000000 : ℝ)*base80 + (210131916503181/133015000000000000000000000000 : ℝ)*base81 + (739753/5000000000000000000000 : ℝ)*base89 + (739753/5000000000000000000000 : ℝ)*base91 + (739753/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41133187112292804995046693/665075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1175570554475243/100000000000000 : ℝ)*(major0) + (1175570554475243/100000000000000 : ℝ)*(major1) + (1175570554475243/100000000000000 : ℝ)*(major2) + (4956419027/100000000000000 : ℝ)*(sp1) + (11602023429/100000000000000 : ℝ)*(sp2) + (298804387/6250000000000 : ℝ)*(sp3) + (1575018394852613/100000000000000 : ℝ)*(sp4) + (787508026094531/50000000000000 : ℝ)*(sp5) + (1575009163161333/100000000000000 : ℝ)*(sp6) + (776113653476891/100000000000000 : ℝ)*(sp7) + (3070688567/100000000000000 : ℝ)*(sp8) + (114233273/25000000000000 : ℝ)*(sp9) + (700356419/100000000000000 : ℝ)*(sp10) + (241400127/20000000000000 : ℝ)*(sp11) + (776119641347717/100000000000000 : ℝ)*(f.failure) + (78751073277059/5000000000000 : ℝ)*(f.sum) + (274293249878137/133015000000000000000000000000 : ℝ)*base66 + (4698374423895370923/1330150000000000000000000000000000 : ℝ)*base68 + (4346158092878620923/1330150000000000000000000000000000 : ℝ)*base70 + (9286478420770320923/1330150000000000000000000000000000 : ℝ)*base72 + (482904423804957/133015000000000000000000000000 : ℝ)*base74 + (11939260249361870923/1330150000000000000000000000000000 : ℝ)*base76 + (6215006847585920923/1330150000000000000000000000000000 : ℝ)*base78 + (12420655301414370923/1330150000000000000000000000000000 : ℝ)*base80 + (171192061530461/66507500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5772733/5000000000000000000000 : ℝ)*base89 + (5772733/5000000000000000000000 : ℝ)*base91 + (5772733/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1244_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27429/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1999/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1244_s2_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052577203/5000000000 : ℝ)*x 0 + (5492448991/10000000000 : ℝ)*x 1 + (5174989683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052577203/5000000000 : ℝ)^8437 ≤ (2555006340003/20000000000000 : ℝ)^6389 := by
    have hnat : (1052577203 : ℕ)^8437*20000000000000^6389 ≤ 2555006340003^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052577203 5000000000 2555006340003 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492448991/10000000000 : ℝ)^8437 ≤ (22663020510113/50000000000000 : ℝ)^6389 := by
    have hnat : (5492448991 : ℕ)^8437*50000000000000^6389 ≤ 22663020510113^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492448991 10000000000 22663020510113 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174989683/10000000000 : ℝ)^8437 ≤ (41898927262563/100000000000000 : ℝ)^6389 := by
    have hnat : (5174989683 : ℕ)^8437*100000000000000^6389 ≤ 41898927262563^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174989683 10000000000 41898927262563 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052577203/5000000000 : ℝ), (5492448991/10000000000 : ℝ), (5174989683/10000000000 : ℝ)] ![(2555006340003/20000000000000 : ℝ), (22663020510113/50000000000000 : ℝ), (41898927262563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052577203/5000000000 : ℝ)|^8437 ≤ (2555006340003/20000000000000 : ℝ)^6389
        have hw : |(-1052577203/5000000000 : ℝ)|=(1052577203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492448991/10000000000 : ℝ)|^8437 ≤ (22663020510113/50000000000000 : ℝ)^6389
        have hw : |(5492448991/10000000000 : ℝ)|=(5492448991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174989683/10000000000 : ℝ)|^8437 ≤ (41898927262563/100000000000000 : ℝ)^6389
        have hw : |(5174989683/10000000000 : ℝ)|=(5174989683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s2_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671200523/1250000000 : ℝ)*x 0 + (-567396163/2500000000 : ℝ)*x 1 + (5174989709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671200523/1250000000 : ℝ)^8437 ≤ (43992132341751/100000000000000 : ℝ)^6389 := by
    have hnat : (671200523 : ℕ)^8437*100000000000000^6389 ≤ 43992132341751^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671200523 1250000000 43992132341751 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (567396163/2500000000 : ℝ)^8437 ≤ (1410894011153/10000000000000 : ℝ)^6389 := by
    have hnat : (567396163 : ℕ)^8437*10000000000000^6389 ≤ 1410894011153^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567396163 2500000000 1410894011153 10000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174989709/10000000000 : ℝ)^8437 ≤ (41898927540549/100000000000000 : ℝ)^6389 := by
    have hnat : (5174989709 : ℕ)^8437*100000000000000^6389 ≤ 41898927540549^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174989709 10000000000 41898927540549 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671200523/1250000000 : ℝ), (-567396163/2500000000 : ℝ), (5174989709/10000000000 : ℝ)] ![(43992132341751/100000000000000 : ℝ), (1410894011153/10000000000000 : ℝ), (41898927540549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671200523/1250000000 : ℝ)|^8437 ≤ (43992132341751/100000000000000 : ℝ)^6389
        have hw : |(671200523/1250000000 : ℝ)|=(671200523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-567396163/2500000000 : ℝ)|^8437 ≤ (1410894011153/10000000000000 : ℝ)^6389
        have hw : |(-567396163/2500000000 : ℝ)|=(567396163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174989709/10000000000 : ℝ)|^8437 ≤ (41898927540549/100000000000000 : ℝ)^6389
        have hw : |(5174989709/10000000000 : ℝ)|=(5174989709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s2_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684802021/5000000000 : ℝ)*x 0 + (2587494909/5000000000 : ℝ)*x 1 + (-283698087/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684802021/5000000000 : ℝ)^8437 ≤ (879842616109/2000000000000 : ℝ)^6389 := by
    have hnat : (2684802021 : ℕ)^8437*2000000000000^6389 ≤ 879842616109^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684802021 5000000000 879842616109 2000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587494909/5000000000 : ℝ)^8437 ≤ (41898928705949/100000000000000 : ℝ)^6389 := by
    have hnat : (2587494909 : ℕ)^8437*100000000000000^6389 ≤ 41898928705949^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587494909 5000000000 41898928705949 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283698087/1250000000 : ℝ)^8437 ≤ (14108940472737/100000000000000 : ℝ)^6389 := by
    have hnat : (283698087 : ℕ)^8437*100000000000000^6389 ≤ 14108940472737^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283698087 1250000000 14108940472737 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684802021/5000000000 : ℝ), (2587494909/5000000000 : ℝ), (-283698087/1250000000 : ℝ)] ![(879842616109/2000000000000 : ℝ), (41898928705949/100000000000000 : ℝ), (14108940472737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684802021/5000000000 : ℝ)|^8437 ≤ (879842616109/2000000000000 : ℝ)^6389
        have hw : |(2684802021/5000000000 : ℝ)|=(2684802021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587494909/5000000000 : ℝ)|^8437 ≤ (41898928705949/100000000000000 : ℝ)^6389
        have hw : |(2587494909/5000000000 : ℝ)|=(2587494909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283698087/1250000000 : ℝ)|^8437 ≤ (14108940472737/100000000000000 : ℝ)^6389
        have hw : |(-283698087/1250000000 : ℝ)|=(283698087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s2_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33920331/78125000 : ℝ)*x 0 + (2015626131/5000000000 : ℝ)*x 1 + (4675489479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33920331/78125000 : ℝ)^8437 ≤ (16614789649871/50000000000000 : ℝ)^6389 := by
    have hnat : (33920331 : ℕ)^8437*50000000000000^6389 ≤ 16614789649871^6389*78125000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33920331 78125000 16614789649871 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015626131/5000000000 : ℝ)^8437 ≤ (30127520195443/100000000000000 : ℝ)^6389 := by
    have hnat : (2015626131 : ℕ)^8437*100000000000000^6389 ≤ 30127520195443^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015626131 5000000000 30127520195443 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4675489479/10000000000 : ℝ)^8437 ≤ (18321450245829/50000000000000 : ℝ)^6389 := by
    have hnat : (4675489479 : ℕ)^8437*50000000000000^6389 ≤ 18321450245829^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4675489479 10000000000 18321450245829 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33920331/78125000 : ℝ), (2015626131/5000000000 : ℝ), (4675489479/10000000000 : ℝ)] ![(16614789649871/50000000000000 : ℝ), (30127520195443/100000000000000 : ℝ), (18321450245829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33920331/78125000 : ℝ)|^8437 ≤ (16614789649871/50000000000000 : ℝ)^6389
        have hw : |(33920331/78125000 : ℝ)|=(33920331/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015626131/5000000000 : ℝ)|^8437 ≤ (30127520195443/100000000000000 : ℝ)^6389
        have hw : |(2015626131/5000000000 : ℝ)|=(2015626131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4675489479/10000000000 : ℝ)|^8437 ≤ (18321450245829/50000000000000 : ℝ)^6389
        have hw : |(4675489479/10000000000 : ℝ)|=(4675489479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s2_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526308103/2500000000 : ℝ)*x 0 + (207081107/400000000 : ℝ)*x 1 + (5490391913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526308103/2500000000 : ℝ)^8437 ≤ (12775656820571/100000000000000 : ℝ)^6389 := by
    have hnat : (526308103 : ℕ)^8437*100000000000000^6389 ≤ 12775656820571^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526308103 2500000000 12775656820571 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207081107/400000000 : ℝ)^8437 ≤ (20960359163887/50000000000000 : ℝ)^6389 := by
    have hnat : (207081107 : ℕ)^8437*50000000000000^6389 ≤ 20960359163887^6389*400000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207081107 400000000 20960359163887 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490391913/10000000000 : ℝ)^8437 ≤ (45303624840343/100000000000000 : ℝ)^6389 := by
    have hnat : (5490391913 : ℕ)^8437*100000000000000^6389 ≤ 45303624840343^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490391913 10000000000 45303624840343 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526308103/2500000000 : ℝ), (207081107/400000000 : ℝ), (5490391913/10000000000 : ℝ)] ![(12775656820571/100000000000000 : ℝ), (20960359163887/50000000000000 : ℝ), (45303624840343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526308103/2500000000 : ℝ)|^8437 ≤ (12775656820571/100000000000000 : ℝ)^6389
        have hw : |(-526308103/2500000000 : ℝ)|=(526308103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207081107/400000000 : ℝ)|^8437 ≤ (20960359163887/50000000000000 : ℝ)^6389
        have hw : |(207081107/400000000 : ℝ)|=(207081107/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490391913/10000000000 : ℝ)|^8437 ≤ (45303624840343/100000000000000 : ℝ)^6389
        have hw : |(5490391913/10000000000 : ℝ)|=(5490391913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s2_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330532723/625000000 : ℝ)*x 0 + (-1954182221/10000000000 : ℝ)*x 1 + (5490391957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330532723/625000000 : ℝ)^8437 ≤ (43117049872507/100000000000000 : ℝ)^6389 := by
    have hnat : (330532723 : ℕ)^8437*100000000000000^6389 ≤ 43117049872507^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330532723 625000000 43117049872507 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1954182221/10000000000 : ℝ)^8437 ≤ (11579324789059/100000000000000 : ℝ)^6389 := by
    have hnat : (1954182221 : ℕ)^8437*100000000000000^6389 ≤ 11579324789059^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954182221 10000000000 11579324789059 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490391957/10000000000 : ℝ)^8437 ≤ (45303625319787/100000000000000 : ℝ)^6389 := by
    have hnat : (5490391957 : ℕ)^8437*100000000000000^6389 ≤ 45303625319787^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490391957 10000000000 45303625319787 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330532723/625000000 : ℝ), (-1954182221/10000000000 : ℝ), (5490391957/10000000000 : ℝ)] ![(43117049872507/100000000000000 : ℝ), (11579324789059/100000000000000 : ℝ), (45303625319787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330532723/625000000 : ℝ)|^8437 ≤ (43117049872507/100000000000000 : ℝ)^6389
        have hw : |(330532723/625000000 : ℝ)|=(330532723/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1954182221/10000000000 : ℝ)|^8437 ≤ (11579324789059/100000000000000 : ℝ)^6389
        have hw : |(-1954182221/10000000000 : ℝ)|=(1954182221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490391957/10000000000 : ℝ)|^8437 ≤ (45303625319787/100000000000000 : ℝ)^6389
        have hw : |(5490391957/10000000000 : ℝ)|=(5490391957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s2_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288523731/10000000000 : ℝ)*x 0 + (2745196021/5000000000 : ℝ)*x 1 + (-1954181879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288523731/10000000000 : ℝ)^8437 ≤ (43117051627427/100000000000000 : ℝ)^6389 := by
    have hnat : (5288523731 : ℕ)^8437*100000000000000^6389 ≤ 43117051627427^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288523731 10000000000 43117051627427 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745196021/5000000000 : ℝ)^8437 ≤ (9060725249197/20000000000000 : ℝ)^6389 := by
    have hnat : (2745196021 : ℕ)^8437*20000000000000^6389 ≤ 9060725249197^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745196021 5000000000 9060725249197 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954181879/10000000000 : ℝ)^8437 ≤ (11579322112977/100000000000000 : ℝ)^6389 := by
    have hnat : (1954181879 : ℕ)^8437*100000000000000^6389 ≤ 11579322112977^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954181879 10000000000 11579322112977 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288523731/10000000000 : ℝ), (2745196021/5000000000 : ℝ), (-1954181879/10000000000 : ℝ)] ![(43117051627427/100000000000000 : ℝ), (9060725249197/20000000000000 : ℝ), (11579322112977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288523731/10000000000 : ℝ)|^8437 ≤ (43117051627427/100000000000000 : ℝ)^6389
        have hw : |(5288523731/10000000000 : ℝ)|=(5288523731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745196021/5000000000 : ℝ)|^8437 ≤ (9060725249197/20000000000000 : ℝ)^6389
        have hw : |(2745196021/5000000000 : ℝ)|=(2745196021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1954181879/10000000000 : ℝ)|^8437 ≤ (11579322112977/100000000000000 : ℝ)^6389
        have hw : |(-1954181879/10000000000 : ℝ)|=(1954181879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s2_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4341960143/10000000000 : ℝ)*x 0 + (4671353959/10000000000 : ℝ)*x 1 + (4035426181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341960143/10000000000 : ℝ)^8437 ≤ (6646234779149/20000000000000 : ℝ)^6389 := by
    have hnat : (4341960143 : ℕ)^8437*20000000000000^6389 ≤ 6646234779149^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341960143 10000000000 6646234779149 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4671353959/10000000000 : ℝ)^8437 ≤ (9150026534757/25000000000000 : ℝ)^6389 := by
    have hnat : (4671353959 : ℕ)^8437*25000000000000^6389 ≤ 9150026534757^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671353959 10000000000 9150026534757 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035426181/10000000000 : ℝ)^8437 ≤ (30168719950649/100000000000000 : ℝ)^6389 := by
    have hnat : (4035426181 : ℕ)^8437*100000000000000^6389 ≤ 30168719950649^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035426181 10000000000 30168719950649 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341960143/10000000000 : ℝ), (4671353959/10000000000 : ℝ), (4035426181/10000000000 : ℝ)] ![(6646234779149/20000000000000 : ℝ), (9150026534757/25000000000000 : ℝ), (30168719950649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341960143/10000000000 : ℝ)|^8437 ≤ (6646234779149/20000000000000 : ℝ)^6389
        have hw : |(4341960143/10000000000 : ℝ)|=(4341960143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4671353959/10000000000 : ℝ)|^8437 ≤ (9150026534757/25000000000000 : ℝ)^6389
        have hw : |(4671353959/10000000000 : ℝ)|=(4671353959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035426181/10000000000 : ℝ)|^8437 ≤ (30168719950649/100000000000000 : ℝ)^6389
        have hw : |(4035426181/10000000000 : ℝ)|=(4035426181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1999/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9507/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8109/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1999/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1999/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1999/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1999/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1999/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1999/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6201/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (1061646815406981/100000000000000000000 : ℝ) := by
    have hpowers : (6201/100000 : ℝ)^2109 ≤ (1061646815406981/100000000000000000000 : ℝ)^512 := by
      have hnat : (6201 : ℕ)^2109*100000000000000000000^512 ≤ 1061646815406981^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6201 100000 1061646815406981 100000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6201/100000 : ℝ)) (X := (1061646815406981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1999/10000 : ℝ) ^ (2109/512 : ℝ) ≤ (32952592245597463/25000000000000000000 : ℝ) := by
    have hpowers : (1999/10000 : ℝ)^2109 ≤ (32952592245597463/25000000000000000000 : ℝ)^512 := by
      have hnat : (1999 : ℕ)^2109*25000000000000000000^512 ≤ 32952592245597463^512*10000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1999 10000 32952592245597463 25000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1999/10000 : ℝ)) (X := (32952592245597463/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001061646815406981/50000000000000000000 : ℝ) ≤ (500002577329539/500000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50001061646815406981/50000000000000000000 : ℝ)^512 ≤ (500002577329539/500000000000000 : ℝ)^2109 := by
      have hnat : (50001061646815406981 : ℕ)^512*500000000000000^2109 ≤ 500002577329539^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001061646815406981 50000000000000000000 500002577329539 500000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500002577329539/500000000000000 : ℝ)) (X := (50001061646815406981/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100132872015797796833/100000000000000000000 : ℝ) ≤ (1250403012531647/1250000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (100132872015797796833/100000000000000000000 : ℝ)^512 ≤ (1250403012531647/1250000000000000 : ℝ)^2109 := by
      have hnat : (100132872015797796833 : ℕ)^512*1250000000000000^2109 ≤ 1250403012531647^2109*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100132872015797796833 100000000000000000000 1250403012531647 1250000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250403012531647/1250000000000000 : ℝ)) (X := (100132872015797796833/100000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12532952592245597463/12500000000000000000 : ℝ) ≤ (2501599163478893/2500000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (12532952592245597463/12500000000000000000 : ℝ)^512 ≤ (2501599163478893/2500000000000000 : ℝ)^2109 := by
      have hnat : (12532952592245597463 : ℕ)^512*2500000000000000^2109 ≤ 2501599163478893^2109*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12532952592245597463 12500000000000000000 2501599163478893 2500000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501599163478893/2500000000000000 : ℝ)) (X := (12532952592245597463/12500000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1061646815406981/100000000000000000000 : ℝ) ≤ ((34462841191354807557/34472500000000000000 : ℝ)+2*(793138415599/344725000000000 : ℝ)*(6201/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (34462841191354807557/34472500000000000000 : ℝ)+2*(793138415599/344725000000000 : ℝ)*(6201/100000 : ℝ)=(500002577329539/500000000000000 : ℝ) by norm_num, show 1+2*(1061646815406981/100000000000000000000 : ℝ)=(50001061646815406981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32952592245597463/25000000000000000000 : ℝ)+(1061646815406981/100000000000000000000 : ℝ) ≤ ((34462841191354807557/34472500000000000000 : ℝ)+(793138415599/344725000000000 : ℝ)*((1999/10000 : ℝ)+(6201/100000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (34462841191354807557/34472500000000000000 : ℝ)+(793138415599/344725000000000 : ℝ)*((1999/10000 : ℝ)+(6201/100000 : ℝ))=(1250403012531647/1250000000000000 : ℝ) by norm_num, show 1+(32952592245597463/25000000000000000000 : ℝ)+(1061646815406981/100000000000000000000 : ℝ)=(100132872015797796833/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32952592245597463/25000000000000000000 : ℝ) ≤ ((34462841191354807557/34472500000000000000 : ℝ)+2*(793138415599/344725000000000 : ℝ)*(1999/10000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (34462841191354807557/34472500000000000000 : ℝ)+2*(793138415599/344725000000000 : ℝ)*(1999/10000 : ℝ)=(2501599163478893/2500000000000000 : ℝ) by norm_num, show 1+2*(32952592245597463/25000000000000000000 : ℝ)=(12532952592245597463/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34462841191354807557/34472500000000000000 : ℝ)*(X 1 0+X 2 0)+(793138415599/344725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (6201/100000 : ℝ)) (hi := (1999/10000 : ℝ)) (c := (34462841191354807557/34472500000000000000 : ℝ)) (alpha := (793138415599/344725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34462841191354807557/34472500000000000000 : ℝ)*(X 0 1+X 2 1)+(793138415599/344725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (6201/100000 : ℝ)) (hi := (1999/10000 : ℝ)) (c := (34462841191354807557/34472500000000000000 : ℝ)) (alpha := (793138415599/344725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34462841191354807557/34472500000000000000 : ℝ)*(X 0 2+X 1 2)+(793138415599/344725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (6201/100000 : ℝ)) (hi := (1999/10000 : ℝ)) (c := (34462841191354807557/34472500000000000000 : ℝ)) (alpha := (793138415599/344725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1052577203/5000000000 : ℝ)*X 0 0+(5492448991/10000000000 : ℝ)*X 0 1+(5174989683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671200523/1250000000 : ℝ)*X 1 0+(-567396163/2500000000 : ℝ)*X 1 1+(5174989709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684802021/5000000000 : ℝ)*X 2 0+(2587494909/5000000000 : ℝ)*X 2 1+(-283698087/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33920331/78125000 : ℝ)*X 0 0+(2015626131/5000000000 : ℝ)*X 0 1+(4675489479/10000000000 : ℝ)*X 0 2+(33920331/78125000 : ℝ)*X 1 0+(2015626131/5000000000 : ℝ)*X 1 1+(4675489479/10000000000 : ℝ)*X 1 2+(33920331/78125000 : ℝ)*X 2 0+(2015626131/5000000000 : ℝ)*X 2 1+(4675489479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-526308103/2500000000 : ℝ)*X 0 0+(207081107/400000000 : ℝ)*X 0 1+(5490391913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330532723/625000000 : ℝ)*X 1 0+(-1954182221/10000000000 : ℝ)*X 1 1+(5490391957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288523731/10000000000 : ℝ)*X 2 0+(2745196021/5000000000 : ℝ)*X 2 1+(-1954181879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341960143/10000000000 : ℝ)*X 0 0+(4671353959/10000000000 : ℝ)*X 0 1+(4035426181/10000000000 : ℝ)*X 0 2+(4341960143/10000000000 : ℝ)*X 1 0+(4671353959/10000000000 : ℝ)*X 1 1+(4035426181/10000000000 : ℝ)*X 1 2+(4341960143/10000000000 : ℝ)*X 2 0+(4671353959/10000000000 : ℝ)*X 2 1+(4035426181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (532110823044409688938724097/53863281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1916652177/100000000000000 : ℝ)*(base19) + (1707291541/100000000000000 : ℝ)*(base23) + (13537529/20000000000000 : ℝ)*(lower2) + (36551681/12500000000000 : ℝ)*(upper3) + (137607491/100000000000000 : ℝ)*(upper5) + (73473405571219/3125000000000 : ℝ)*(major0) + (73473405571219/3125000000000 : ℝ)*(major1) + (73473405571219/3125000000000 : ℝ)*(major2) + (393754104971353/12500000000000 : ℝ)*(sp0) + (1575025616264609/50000000000000 : ℝ)*(sp1) + (1575025720944927/50000000000000 : ℝ)*(sp2) + (776116537838233/50000000000000 : ℝ)*(sp3) + (2030941057/10000000000000 : ℝ)*(sp4) + (1425300369/12500000000000 : ℝ)*(sp7) + (776122239039709/50000000000000 : ℝ)*(f.failure) + (1575026574590697/50000000000000 : ℝ)*(f.sum) + (9770484345227/4309062500000000000000000000 : ℝ)*base66 + (294127231574131821/53863281250000000000000000000000 : ℝ)*base68 + (580961410847685517/107726562500000000000000000000000 : ℝ)*base70 + (1837241113311060517/107726562500000000000000000000000 : ℝ)*base72 + (67268781381997/17236250000000000000000000000 : ℝ)*base73 + (751458987379248017/107726562500000000000000000000000 : ℝ)*base76 + (1005822774822654267/107726562500000000000000000000000 : ℝ)*base78 + (841405770248123017/107726562500000000000000000000000 : ℝ)*base80 + (6128239396011/34472500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (26409941/2500000000000000000000 : ℝ)*base89 + (26409941/2500000000000000000000 : ℝ)*base91 + (26409941/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58865528875369362476709/8618125000000000000000000000 : ℝ) := by norm_num
    linear_combination (880026591/50000000000000 : ℝ)*(base19) + (404153377/20000000000000 : ℝ)*(base23) + (36582727/100000000000000 : ℝ)*(upper2) + (60223097/25000000000000 : ℝ)*(upper3) + (66743281/50000000000000 : ℝ)*(upper5) + (2381839857223621/100000000000000 : ℝ)*(major0) + (2381839857223621/100000000000000 : ℝ)*(major1) + (2381839857223621/100000000000000 : ℝ)*(major2) + (17972724467/100000000000000 : ℝ)*(sp1) + (12025373467/50000000000000 : ℝ)*(sp2) + (638234536512101/20000000000000 : ℝ)*(sp4) + (398894118722857/12500000000000 : ℝ)*(sp5) + (1595573305523343/50000000000000 : ℝ)*(sp6) + (1572506804205621/100000000000000 : ℝ)*(sp7) + (1572506804205621/100000000000000 : ℝ)*(f.failure) + (638234536512101/20000000000000 : ℝ)*(f.sum) + (57756565554781/68945000000000000000000000000 : ℝ)*base65 + (9914461684256103897/3447250000000000000000000000000000 : ℝ)*base67 + (5141678650000896103/3447250000000000000000000000000000 : ℝ)*base70 + (12868084439550146103/3447250000000000000000000000000000 : ℝ)*base72 + (147864637598261/68945000000000000000000000000 : ℝ)*base73 + (19314023984618396103/3447250000000000000000000000000000 : ℝ)*base76 + (3455704139884353897/3447250000000000000000000000000000 : ℝ)*base77 + (14731597301315853897/3447250000000000000000000000000000 : ℝ)*base79 + (27029416902219/68945000000000000000000000000 : ℝ)*base82 + (15765229/5000000000000000000000 : ℝ)*base89 + (15765229/5000000000000000000000 : ℝ)*base91 + (15765229/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1244_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1999/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9507/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8109/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1244_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9507/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8109/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1244_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1244_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1244_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9507/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8109/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1244_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
