-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1181_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:28.389996+00:00
-- url     : https://prove2.me/submissions/249a23b4-eb10-4e40-bedb-ad69d584be1e

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
theorem support_rectangle_w1181_box_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2022749439/10000000000 : ℝ)*x 0 + (5375748999/10000000000 : ℝ)*x 1 + (5375749197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022749439/10000000000 : ℝ)^4187 ≤ (12057173316037/100000000000000 : ℝ)^3163 := by
    have hnat : (2022749439 : ℕ)^4187*100000000000000^3163 ≤ 12057173316037^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022749439 10000000000 12057173316037 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375748999/10000000000 : ℝ)^4187 ≤ (8794282451873/20000000000000 : ℝ)^3163 := by
    have hnat : (5375748999 : ℕ)^4187*20000000000000^3163 ≤ 8794282451873^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375748999 10000000000 8794282451873 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375749197/10000000000 : ℝ)^4187 ≤ (8794282880649/20000000000000 : ℝ)^3163 := by
    have hnat : (5375749197 : ℕ)^4187*20000000000000^3163 ≤ 8794282880649^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375749197 10000000000 8794282880649 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2022749439/10000000000 : ℝ), (5375748999/10000000000 : ℝ), (5375749197/10000000000 : ℝ)] ![(12057173316037/100000000000000 : ℝ), (8794282451873/20000000000000 : ℝ), (8794282880649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2022749439/10000000000 : ℝ)|^4187 ≤ (12057173316037/100000000000000 : ℝ)^3163
        have hw : |(-2022749439/10000000000 : ℝ)|=(2022749439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375748999/10000000000 : ℝ)|^4187 ≤ (8794282451873/20000000000000 : ℝ)^3163
        have hw : |(5375748999/10000000000 : ℝ)|=(5375748999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375749197/10000000000 : ℝ)|^4187 ≤ (8794282880649/20000000000000 : ℝ)^3163
        have hw : |(5375749197/10000000000 : ℝ)|=(5375749197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529632841/1000000000 : ℝ)*x 0 + (-2130552861/10000000000 : ℝ)*x 1 + (5375748887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529632841/1000000000 : ℝ)^4187 ≤ (43113535368003/100000000000000 : ℝ)^3163 := by
    have hnat : (529632841 : ℕ)^4187*100000000000000^3163 ≤ 43113535368003^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529632841 1000000000 43113535368003 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130552861/10000000000 : ℝ)^4187 ≤ (12915053571033/100000000000000 : ℝ)^3163 := by
    have hnat : (2130552861 : ℕ)^4187*100000000000000^3163 ≤ 12915053571033^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130552861 10000000000 12915053571033 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375748887/10000000000 : ℝ)^4187 ≤ (21985705523333/50000000000000 : ℝ)^3163 := by
    have hnat : (5375748887 : ℕ)^4187*50000000000000^3163 ≤ 21985705523333^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375748887 10000000000 21985705523333 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529632841/1000000000 : ℝ), (-2130552861/10000000000 : ℝ), (5375748887/10000000000 : ℝ)] ![(43113535368003/100000000000000 : ℝ), (12915053571033/100000000000000 : ℝ), (21985705523333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529632841/1000000000 : ℝ)|^4187 ≤ (43113535368003/100000000000000 : ℝ)^3163
        have hw : |(529632841/1000000000 : ℝ)|=(529632841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130552861/10000000000 : ℝ)|^4187 ≤ (12915053571033/100000000000000 : ℝ)^3163
        have hw : |(-2130552861/10000000000 : ℝ)|=(2130552861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375748887/10000000000 : ℝ)|^4187 ≤ (21985705523333/50000000000000 : ℝ)^3163
        have hw : |(5375748887/10000000000 : ℝ)|=(5375748887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296329347/10000000000 : ℝ)*x 0 + (2687874109/5000000000 : ℝ)*x 1 + (-266319063/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296329347/10000000000 : ℝ)^4187 ≤ (8622709092953/20000000000000 : ℝ)^3163 := by
    have hnat : (5296329347 : ℕ)^4187*20000000000000^3163 ≤ 8622709092953^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296329347 10000000000 8622709092953 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687874109/5000000000 : ℝ)^4187 ≤ (43971403802951/100000000000000 : ℝ)^3163 := by
    have hnat : (2687874109 : ℕ)^4187*100000000000000^3163 ≤ 43971403802951^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687874109 5000000000 43971403802951 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266319063/1250000000 : ℝ)^4187 ≤ (6457525353177/50000000000000 : ℝ)^3163 := by
    have hnat : (266319063 : ℕ)^4187*50000000000000^3163 ≤ 6457525353177^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266319063 1250000000 6457525353177 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296329347/10000000000 : ℝ), (2687874109/5000000000 : ℝ), (-266319063/1250000000 : ℝ)] ![(8622709092953/20000000000000 : ℝ), (43971403802951/100000000000000 : ℝ), (6457525353177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296329347/10000000000 : ℝ)|^4187 ≤ (8622709092953/20000000000000 : ℝ)^3163
        have hw : |(5296329347/10000000000 : ℝ)|=(5296329347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687874109/5000000000 : ℝ)|^4187 ≤ (43971403802951/100000000000000 : ℝ)^3163
        have hw : |(2687874109/5000000000 : ℝ)|=(2687874109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266319063/1250000000 : ℝ)|^4187 ≤ (6457525353177/50000000000000 : ℝ)^3163
        have hw : |(-266319063/1250000000 : ℝ)|=(266319063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (893269669/2000000000 : ℝ)*x 0 + (430772251/1000000000 : ℝ)*x 1 + (538465243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893269669/2000000000 : ℝ)^4187 ≤ (17202719177621/50000000000000 : ℝ)^3163 := by
    have hnat : (893269669 : ℕ)^4187*50000000000000^3163 ≤ 17202719177621^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893269669 2000000000 17202719177621 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430772251/1000000000 : ℝ)^4187 ≤ (4099660458299/12500000000000 : ℝ)^3163 := by
    have hnat : (430772251 : ℕ)^4187*12500000000000^3163 ≤ 4099660458299^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430772251 1000000000 4099660458299 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538465243/1250000000 : ℝ)^4187 ≤ (32797277961987/100000000000000 : ℝ)^3163 := by
    have hnat : (538465243 : ℕ)^4187*100000000000000^3163 ≤ 32797277961987^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538465243 1250000000 32797277961987 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(893269669/2000000000 : ℝ), (430772251/1000000000 : ℝ), (538465243/1250000000 : ℝ)] ![(17202719177621/50000000000000 : ℝ), (4099660458299/12500000000000 : ℝ), (32797277961987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(893269669/2000000000 : ℝ)|^4187 ≤ (17202719177621/50000000000000 : ℝ)^3163
        have hw : |(893269669/2000000000 : ℝ)|=(893269669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430772251/1000000000 : ℝ)|^4187 ≤ (4099660458299/12500000000000 : ℝ)^3163
        have hw : |(430772251/1000000000 : ℝ)|=(430772251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538465243/1250000000 : ℝ)|^4187 ≤ (32797277961987/100000000000000 : ℝ)^3163
        have hw : |(538465243/1250000000 : ℝ)|=(538465243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-568846157/2500000000 : ℝ)*x 0 + (1056323489/2000000000 : ℝ)*x 1 + (5281617453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (568846157/2500000000 : ℝ)^4187 ≤ (14089826235797/100000000000000 : ℝ)^3163 := by
    have hnat : (568846157 : ℕ)^4187*100000000000000^3163 ≤ 14089826235797^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568846157 2500000000 14089826235797 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056323489/2000000000 : ℝ)^4187 ≤ (42955086831709/100000000000000 : ℝ)^3163 := by
    have hnat : (1056323489 : ℕ)^4187*100000000000000^3163 ≤ 42955086831709^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056323489 2000000000 42955086831709 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281617453/10000000000 : ℝ)^4187 ≤ (42955086917837/100000000000000 : ℝ)^3163 := by
    have hnat : (5281617453 : ℕ)^4187*100000000000000^3163 ≤ 42955086917837^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281617453 10000000000 42955086917837 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-568846157/2500000000 : ℝ), (1056323489/2000000000 : ℝ), (5281617453/10000000000 : ℝ)] ![(14089826235797/100000000000000 : ℝ), (42955086831709/100000000000000 : ℝ), (42955086917837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-568846157/2500000000 : ℝ)|^4187 ≤ (14089826235797/100000000000000 : ℝ)^3163
        have hw : |(-568846157/2500000000 : ℝ)|=(568846157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056323489/2000000000 : ℝ)|^4187 ≤ (42955086831709/100000000000000 : ℝ)^3163
        have hw : |(1056323489/2000000000 : ℝ)|=(1056323489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281617453/10000000000 : ℝ)|^4187 ≤ (42955086917837/100000000000000 : ℝ)^3163
        have hw : |(5281617453/10000000000 : ℝ)|=(5281617453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362774497/10000000000 : ℝ)*x 0 + (-216769481/1000000000 : ℝ)*x 1 + (5281617431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362774497/10000000000 : ℝ)^4187 ≤ (43830983486211/100000000000000 : ℝ)^3163 := by
    have hnat : (5362774497 : ℕ)^4187*100000000000000^3163 ≤ 43830983486211^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362774497 10000000000 43830983486211 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216769481/1000000000 : ℝ)^4187 ≤ (13213929819001/100000000000000 : ℝ)^3163 := by
    have hnat : (216769481 : ℕ)^4187*100000000000000^3163 ≤ 13213929819001^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216769481 1000000000 13213929819001 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281617431/10000000000 : ℝ)^4187 ≤ (42955086680987/100000000000000 : ℝ)^3163 := by
    have hnat : (5281617431 : ℕ)^4187*100000000000000^3163 ≤ 42955086680987^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281617431 10000000000 42955086680987 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362774497/10000000000 : ℝ), (-216769481/1000000000 : ℝ), (5281617431/10000000000 : ℝ)] ![(43830983486211/100000000000000 : ℝ), (13213929819001/100000000000000 : ℝ), (42955086680987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362774497/10000000000 : ℝ)|^4187 ≤ (43830983486211/100000000000000 : ℝ)^3163
        have hw : |(5362774497/10000000000 : ℝ)|=(5362774497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216769481/1000000000 : ℝ)|^4187 ≤ (13213929819001/100000000000000 : ℝ)^3163
        have hw : |(-216769481/1000000000 : ℝ)|=(216769481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281617431/10000000000 : ℝ)|^4187 ≤ (42955086680987/100000000000000 : ℝ)^3163
        have hw : |(5281617431/10000000000 : ℝ)|=(5281617431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681387293/5000000000 : ℝ)*x 0 + (5281617441/10000000000 : ℝ)*x 1 + (-2167694677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681387293/5000000000 : ℝ)^4187 ≤ (43830984449121/100000000000000 : ℝ)^3163 := by
    have hnat : (2681387293 : ℕ)^4187*100000000000000^3163 ≤ 43830984449121^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681387293 5000000000 43830984449121 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281617441/10000000000 : ℝ)^4187 ≤ (21477543394323/50000000000000 : ℝ)^3163 := by
    have hnat : (5281617441 : ℕ)^4187*50000000000000^3163 ≤ 21477543394323^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281617441 10000000000 21477543394323 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2167694677/10000000000 : ℝ)^4187 ≤ (660696437289/5000000000000 : ℝ)^3163 := by
    have hnat : (2167694677 : ℕ)^4187*5000000000000^3163 ≤ 660696437289^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167694677 10000000000 660696437289 5000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681387293/5000000000 : ℝ), (5281617441/10000000000 : ℝ), (-2167694677/10000000000 : ℝ)] ![(43830984449121/100000000000000 : ℝ), (21477543394323/50000000000000 : ℝ), (660696437289/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681387293/5000000000 : ℝ)|^4187 ≤ (43830984449121/100000000000000 : ℝ)^3163
        have hw : |(2681387293/5000000000 : ℝ)|=(2681387293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281617441/10000000000 : ℝ)|^4187 ≤ (21477543394323/50000000000000 : ℝ)^3163
        have hw : |(5281617441/10000000000 : ℝ)|=(5281617441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2167694677/10000000000 : ℝ)|^4187 ≤ (660696437289/5000000000000 : ℝ)^3163
        have hw : |(-2167694677/10000000000 : ℝ)|=(2167694677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850338681/2000000000 : ℝ)*x 0 + (4415029083/10000000000 : ℝ)*x 1 + (220751461/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850338681/2000000000 : ℝ)^4187 ≤ (1007305915671/3125000000000 : ℝ)^3163 := by
    have hnat : (850338681 : ℕ)^4187*3125000000000^3163 ≤ 1007305915671^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850338681 2000000000 1007305915671 3125000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4415029083/10000000000 : ℝ)^4187 ≤ (1694155232237/5000000000000 : ℝ)^3163 := by
    have hnat : (4415029083 : ℕ)^4187*5000000000000^3163 ≤ 1694155232237^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415029083 10000000000 1694155232237 5000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220751461/500000000 : ℝ)^4187 ≤ (33883106036531/100000000000000 : ℝ)^3163 := by
    have hnat : (220751461 : ℕ)^4187*100000000000000^3163 ≤ 33883106036531^3163*500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220751461 500000000 33883106036531 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850338681/2000000000 : ℝ), (4415029083/10000000000 : ℝ), (220751461/500000000 : ℝ)] ![(1007305915671/3125000000000 : ℝ), (1694155232237/5000000000000 : ℝ), (33883106036531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850338681/2000000000 : ℝ)|^4187 ≤ (1007305915671/3125000000000 : ℝ)^3163
        have hw : |(850338681/2000000000 : ℝ)|=(850338681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4415029083/10000000000 : ℝ)|^4187 ≤ (1694155232237/5000000000000 : ℝ)^3163
        have hw : |(4415029083/10000000000 : ℝ)|=(4415029083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220751461/500000000 : ℝ)|^4187 ≤ (33883106036531/100000000000000 : ℝ)^3163
        have hw : |(220751461/500000000 : ℝ)|=(220751461/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_8 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2222511003/10000000000 : ℝ)*x 0 + (652190563/1250000000 : ℝ)*x 1 + (5385360593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2222511003/10000000000 : ℝ)^4187 ≤ (3414515083137/25000000000000 : ℝ)^3163 := by
    have hnat : (2222511003 : ℕ)^4187*25000000000000^3163 ≤ 3414515083137^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222511003 10000000000 3414515083137 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652190563/1250000000 : ℝ)^4187 ≤ (42266426062917/100000000000000 : ℝ)^3163 := by
    have hnat : (652190563 : ℕ)^4187*100000000000000^3163 ≤ 42266426062917^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652190563 1250000000 42266426062917 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385360593/10000000000 : ℝ)^4187 ≤ (22037756790427/50000000000000 : ℝ)^3163 := by
    have hnat : (5385360593 : ℕ)^4187*50000000000000^3163 ≤ 22037756790427^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385360593 10000000000 22037756790427 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2222511003/10000000000 : ℝ), (652190563/1250000000 : ℝ), (5385360593/10000000000 : ℝ)] ![(3414515083137/25000000000000 : ℝ), (42266426062917/100000000000000 : ℝ), (22037756790427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2222511003/10000000000 : ℝ)|^4187 ≤ (3414515083137/25000000000000 : ℝ)^3163
        have hw : |(-2222511003/10000000000 : ℝ)|=(2222511003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652190563/1250000000 : ℝ)|^4187 ≤ (42266426062917/100000000000000 : ℝ)^3163
        have hw : |(652190563/1250000000 : ℝ)|=(652190563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385360593/10000000000 : ℝ)|^4187 ≤ (22037756790427/50000000000000 : ℝ)^3163
        have hw : |(5385360593/10000000000 : ℝ)|=(5385360593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_9 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289541067/10000000000 : ℝ)*x 0 + (-2126691293/10000000000 : ℝ)*x 1 + (134634009/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289541067/10000000000 : ℝ)^4187 ≤ (5380051584527/12500000000000 : ℝ)^3163 := by
    have hnat : (5289541067 : ℕ)^4187*12500000000000^3163 ≤ 5380051584527^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289541067 10000000000 5380051584527 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126691293/10000000000 : ℝ)^4187 ≤ (12884076249301/100000000000000 : ℝ)^3163 := by
    have hnat : (2126691293 : ℕ)^4187*100000000000000^3163 ≤ 12884076249301^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126691293 10000000000 12884076249301 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134634009/250000000 : ℝ)^4187 ≤ (44075511056547/100000000000000 : ℝ)^3163 := by
    have hnat : (134634009 : ℕ)^4187*100000000000000^3163 ≤ 44075511056547^3163*250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134634009 250000000 44075511056547 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289541067/10000000000 : ℝ), (-2126691293/10000000000 : ℝ), (134634009/250000000 : ℝ)] ![(5380051584527/12500000000000 : ℝ), (12884076249301/100000000000000 : ℝ), (44075511056547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289541067/10000000000 : ℝ)|^4187 ≤ (5380051584527/12500000000000 : ℝ)^3163
        have hw : |(5289541067/10000000000 : ℝ)|=(5289541067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126691293/10000000000 : ℝ)|^4187 ≤ (12884076249301/100000000000000 : ℝ)^3163
        have hw : |(-2126691293/10000000000 : ℝ)|=(2126691293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134634009/250000000 : ℝ)|^4187 ≤ (44075511056547/100000000000000 : ℝ)^3163
        have hw : |(134634009/250000000 : ℝ)|=(134634009/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_10 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330596313/625000000 : ℝ)*x 0 + (5385360123/10000000000 : ℝ)*x 1 + (-531672923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330596313/625000000 : ℝ)^4187 ≤ (43040412040717/100000000000000 : ℝ)^3163 := by
    have hnat : (330596313 : ℕ)^4187*100000000000000^3163 ≤ 43040412040717^3163*625000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330596313 625000000 43040412040717 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385360123/10000000000 : ℝ)^4187 ≤ (44075508488903/100000000000000 : ℝ)^3163 := by
    have hnat : (5385360123 : ℕ)^4187*100000000000000^3163 ≤ 44075508488903^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385360123 10000000000 44075508488903 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531672923/2500000000 : ℝ)^4187 ≤ (80525496557/625000000000 : ℝ)^3163 := by
    have hnat : (531672923 : ℕ)^4187*625000000000^3163 ≤ 80525496557^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531672923 2500000000 80525496557 625000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330596313/625000000 : ℝ), (5385360123/10000000000 : ℝ), (-531672923/2500000000 : ℝ)] ![(43040412040717/100000000000000 : ℝ), (44075508488903/100000000000000 : ℝ), (80525496557/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330596313/625000000 : ℝ)|^4187 ≤ (43040412040717/100000000000000 : ℝ)^3163
        have hw : |(330596313/625000000 : ℝ)|=(330596313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385360123/10000000000 : ℝ)|^4187 ≤ (44075508488903/100000000000000 : ℝ)^3163
        have hw : |(5385360123/10000000000 : ℝ)|=(5385360123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531672923/2500000000 : ℝ)|^4187 ≤ (80525496557/625000000000 : ℝ)^3163
        have hw : |(-531672923/2500000000 : ℝ)|=(531672923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_11 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2243996833/5000000000 : ℝ)*x 0 + (214837951/500000000 : ℝ)*x 1 + (4296759019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243996833/5000000000 : ℝ)^4187 ≤ (17313165815093/50000000000000 : ℝ)^3163 := by
    have hnat : (2243996833 : ℕ)^4187*50000000000000^3163 ≤ 17313165815093^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243996833 5000000000 17313165815093 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214837951/500000000 : ℝ)^4187 ≤ (32686834182281/100000000000000 : ℝ)^3163 := by
    have hnat : (214837951 : ℕ)^4187*100000000000000^3163 ≤ 32686834182281^3163*500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214837951 500000000 32686834182281 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4296759019/10000000000 : ℝ)^4187 ≤ (32686834172211/100000000000000 : ℝ)^3163 := by
    have hnat : (4296759019 : ℕ)^4187*100000000000000^3163 ≤ 32686834172211^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296759019 10000000000 32686834172211 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243996833/5000000000 : ℝ), (214837951/500000000 : ℝ), (4296759019/10000000000 : ℝ)] ![(17313165815093/50000000000000 : ℝ), (32686834182281/100000000000000 : ℝ), (32686834172211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243996833/5000000000 : ℝ)|^4187 ≤ (17313165815093/50000000000000 : ℝ)^3163
        have hw : |(2243996833/5000000000 : ℝ)|=(2243996833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(214837951/500000000 : ℝ)|^4187 ≤ (32686834182281/100000000000000 : ℝ)^3163
        have hw : |(214837951/500000000 : ℝ)|=(214837951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4296759019/10000000000 : ℝ)|^4187 ≤ (32686834172211/100000000000000 : ℝ)^3163
        have hw : |(4296759019/10000000000 : ℝ)|=(4296759019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_12 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075919143/10000000000 : ℝ)*x 0 + (5438591719/10000000000 : ℝ)*x 1 + (1318390337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075919143/10000000000 : ℝ)^4187 ≤ (499139443167/4000000000000 : ℝ)^3163 := by
    have hnat : (2075919143 : ℕ)^4187*4000000000000^3163 ≤ 499139443167^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075919143 10000000000 499139443167 4000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438591719/10000000000 : ℝ)^4187 ≤ (44653137001933/100000000000000 : ℝ)^3163 := by
    have hnat : (5438591719 : ℕ)^4187*100000000000000^3163 ≤ 44653137001933^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438591719 10000000000 44653137001933 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318390337/2500000000 : ℝ)^4187 ≤ (42868376901583/100000000000000 : ℝ)^3163 := by
    have hnat : (1318390337 : ℕ)^4187*100000000000000^3163 ≤ 42868376901583^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318390337 2500000000 42868376901583 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075919143/10000000000 : ℝ), (5438591719/10000000000 : ℝ), (1318390337/2500000000 : ℝ)] ![(499139443167/4000000000000 : ℝ), (44653137001933/100000000000000 : ℝ), (42868376901583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075919143/10000000000 : ℝ)|^4187 ≤ (499139443167/4000000000000 : ℝ)^3163
        have hw : |(-2075919143/10000000000 : ℝ)|=(2075919143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438591719/10000000000 : ℝ)|^4187 ≤ (44653137001933/100000000000000 : ℝ)^3163
        have hw : |(5438591719/10000000000 : ℝ)|=(5438591719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318390337/2500000000 : ℝ)|^4187 ≤ (42868376901583/100000000000000 : ℝ)^3163
        have hw : |(1318390337/2500000000 : ℝ)|=(1318390337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_13 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073691731/2000000000 : ℝ)*x 0 + (-2170817163/10000000000 : ℝ)*x 1 + (1054712269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073691731/2000000000 : ℝ)^4187 ≤ (21946246059891/50000000000000 : ℝ)^3163 := by
    have hnat : (1073691731 : ℕ)^4187*50000000000000^3163 ≤ 21946246059891^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073691731 2000000000 21946246059891 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170817163/10000000000 : ℝ)^4187 ≤ (2647826199421/20000000000000 : ℝ)^3163 := by
    have hnat : (2170817163 : ℕ)^4187*20000000000000^3163 ≤ 2647826199421^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170817163 10000000000 2647826199421 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054712269/2000000000 : ℝ)^4187 ≤ (21434188434651/50000000000000 : ℝ)^3163 := by
    have hnat : (1054712269 : ℕ)^4187*50000000000000^3163 ≤ 21434188434651^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054712269 2000000000 21434188434651 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073691731/2000000000 : ℝ), (-2170817163/10000000000 : ℝ), (1054712269/2000000000 : ℝ)] ![(21946246059891/50000000000000 : ℝ), (2647826199421/20000000000000 : ℝ), (21434188434651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073691731/2000000000 : ℝ)|^4187 ≤ (21946246059891/50000000000000 : ℝ)^3163
        have hw : |(1073691731/2000000000 : ℝ)|=(1073691731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170817163/10000000000 : ℝ)|^4187 ≤ (2647826199421/20000000000000 : ℝ)^3163
        have hw : |(-2170817163/10000000000 : ℝ)|=(2170817163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054712269/2000000000 : ℝ)|^4187 ≤ (21434188434651/50000000000000 : ℝ)^3163
        have hw : |(1054712269/2000000000 : ℝ)|=(1054712269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_14 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368458653/10000000000 : ℝ)*x 0 + (2636780999/5000000000 : ℝ)*x 1 + (-1085408147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368458653/10000000000 : ℝ)^4187 ≤ (5486561512267/12500000000000 : ℝ)^3163 := by
    have hnat : (5368458653 : ℕ)^4187*12500000000000^3163 ≤ 5486561512267^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368458653 10000000000 5486561512267 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636780999/5000000000 : ℝ)^4187 ≤ (42868383895979/100000000000000 : ℝ)^3163 := by
    have hnat : (2636780999 : ℕ)^4187*100000000000000^3163 ≤ 42868383895979^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636780999 5000000000 42868383895979 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085408147/5000000000 : ℝ)^4187 ≤ (13239123981587/100000000000000 : ℝ)^3163 := by
    have hnat : (1085408147 : ℕ)^4187*100000000000000^3163 ≤ 13239123981587^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085408147 5000000000 13239123981587 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368458653/10000000000 : ℝ), (2636780999/5000000000 : ℝ), (-1085408147/5000000000 : ℝ)] ![(5486561512267/12500000000000 : ℝ), (42868383895979/100000000000000 : ℝ), (13239123981587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368458653/10000000000 : ℝ)|^4187 ≤ (5486561512267/12500000000000 : ℝ)^3163
        have hw : |(5368458653/10000000000 : ℝ)|=(5368458653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636780999/5000000000 : ℝ)|^4187 ≤ (42868383895979/100000000000000 : ℝ)^3163
        have hw : |(2636780999/5000000000 : ℝ)|=(2636780999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085408147/5000000000 : ℝ)|^4187 ≤ (13239123981587/100000000000000 : ℝ)^3163
        have hw : |(-1085408147/5000000000 : ℝ)|=(1085408147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_box_15 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2116545761/5000000000 : ℝ)*x 0 + (2212103867/5000000000 : ℝ)*x 1 + (4424207609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116545761/5000000000 : ℝ)^4187 ≤ (32047236354747/100000000000000 : ℝ)^3163 := by
    have hnat : (2116545761 : ℕ)^4187*100000000000000^3163 ≤ 32047236354747^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116545761 5000000000 32047236354747 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212103867/5000000000 : ℝ)^4187 ≤ (16988191224229/50000000000000 : ℝ)^3163 := by
    have hnat : (2212103867 : ℕ)^4187*50000000000000^3163 ≤ 16988191224229^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212103867 5000000000 16988191224229 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4424207609/10000000000 : ℝ)^4187 ≤ (16988190588861/50000000000000 : ℝ)^3163 := by
    have hnat : (4424207609 : ℕ)^4187*50000000000000^3163 ≤ 16988190588861^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424207609 10000000000 16988190588861 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116545761/5000000000 : ℝ), (2212103867/5000000000 : ℝ), (4424207609/10000000000 : ℝ)] ![(32047236354747/100000000000000 : ℝ), (16988191224229/50000000000000 : ℝ), (16988190588861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116545761/5000000000 : ℝ)|^4187 ≤ (32047236354747/100000000000000 : ℝ)^3163
        have hw : |(2116545761/5000000000 : ℝ)|=(2116545761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2212103867/5000000000 : ℝ)|^4187 ≤ (16988191224229/50000000000000 : ℝ)^3163
        have hw : |(2212103867/5000000000 : ℝ)|=(2212103867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4424207609/10000000000 : ℝ)|^4187 ≤ (16988190588861/50000000000000 : ℝ)^3163
        have hw : |(4424207609/10000000000 : ℝ)|=(4424207609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15559/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59329/100000 : ℝ) ∧ (79927/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83211/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2851/25000 : ℝ) ^ (8373/2048 : ℝ) ≤ (13960230272681679/100000000000000000000 : ℝ) := by
    have hpowers : (2851/25000 : ℝ)^8373 ≤ (13960230272681679/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2851 : ℕ)^8373*100000000000000000000^2048 ≤ 13960230272681679^2048*25000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2851 25000 13960230272681679 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2851/25000 : ℝ)) (X := (13960230272681679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14071/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (16481614361040373/50000000000000000000 : ℝ) := by
    have hpowers : (14071/100000 : ℝ)^8373 ≤ (16481614361040373/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14071 : ℕ)^8373*50000000000000000000^2048 ≤ 16481614361040373^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14071 100000 16481614361040373 50000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14071/100000 : ℝ)) (X := (16481614361040373/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013960230272681679/50000000000000000000 : ℝ) ≤ (10000682850520499/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50013960230272681679/50000000000000000000 : ℝ)^2048 ≤ (10000682850520499/10000000000000000 : ℝ)^8373 := by
      have hnat : (50013960230272681679 : ℕ)^2048*10000000000000000^8373 ≤ 10000682850520499^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013960230272681679 50000000000000000000 10000682850520499 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000682850520499/10000000000000000 : ℝ)) (X := (50013960230272681679/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001876938359790497/4000000000000000000 : ℝ) ≤ (2500286881096799/2500000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (4001876938359790497/4000000000000000000 : ℝ)^2048 ≤ (2500286881096799/2500000000000000 : ℝ)^8373 := by
      have hnat : (4001876938359790497 : ℕ)^2048*2500000000000000^8373 ≤ 2500286881096799^8373*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001876938359790497 4000000000000000000 2500286881096799 2500000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500286881096799/2500000000000000 : ℝ)) (X := (4001876938359790497/4000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016481614361040373/25000000000000000000 : ℝ) ≤ (10001612198253893/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (25016481614361040373/25000000000000000000 : ℝ)^2048 ≤ (10001612198253893/10000000000000000 : ℝ)^8373 := by
      have hnat : (25016481614361040373 : ℕ)^2048*10000000000000000^8373 ≤ 10001612198253893^8373*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016481614361040373 25000000000000000000 10001612198253893 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001612198253893/10000000000000000 : ℝ)) (X := (25016481614361040373/25000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13960230272681679/100000000000000000000 : ℝ) ≤ ((8887074293595515219/8890000000000000000 : ℝ)+2*(154891288899/88900000000000 : ℝ)*(2851/25000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (8887074293595515219/8890000000000000000 : ℝ)+2*(154891288899/88900000000000 : ℝ)*(2851/25000 : ℝ)=(10000682850520499/10000000000000000 : ℝ) by norm_num, show 1+2*(13960230272681679/100000000000000000000 : ℝ)=(50013960230272681679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16481614361040373/50000000000000000000 : ℝ)+(13960230272681679/100000000000000000000 : ℝ) ≤ ((8887074293595515219/8890000000000000000 : ℝ)+(154891288899/88900000000000 : ℝ)*((14071/100000 : ℝ)+(2851/25000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (8887074293595515219/8890000000000000000 : ℝ)+(154891288899/88900000000000 : ℝ)*((14071/100000 : ℝ)+(2851/25000 : ℝ))=(2500286881096799/2500000000000000 : ℝ) by norm_num, show 1+(16481614361040373/50000000000000000000 : ℝ)+(13960230272681679/100000000000000000000 : ℝ)=(4001876938359790497/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16481614361040373/50000000000000000000 : ℝ) ≤ ((8887074293595515219/8890000000000000000 : ℝ)+2*(154891288899/88900000000000 : ℝ)*(14071/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (8887074293595515219/8890000000000000000 : ℝ)+2*(154891288899/88900000000000 : ℝ)*(14071/100000 : ℝ)=(10001612198253893/10000000000000000 : ℝ) by norm_num, show 1+2*(16481614361040373/50000000000000000000 : ℝ)=(25016481614361040373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8887074293595515219/8890000000000000000 : ℝ)*(X 1 0+X 2 0)+(154891288899/88900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (8887074293595515219/8890000000000000000 : ℝ)) (alpha := (154891288899/88900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8887074293595515219/8890000000000000000 : ℝ)*(X 0 1+X 2 1)+(154891288899/88900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (8887074293595515219/8890000000000000000 : ℝ)) (alpha := (154891288899/88900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8887074293595515219/8890000000000000000 : ℝ)*(X 0 2+X 1 2)+(154891288899/88900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (8887074293595515219/8890000000000000000 : ℝ)) (alpha := (154891288899/88900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2022749439/10000000000 : ℝ)*X 0 0+(5375748999/10000000000 : ℝ)*X 0 1+(5375749197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((529632841/1000000000 : ℝ)*X 1 0+(-2130552861/10000000000 : ℝ)*X 1 1+(5375748887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296329347/10000000000 : ℝ)*X 2 0+(2687874109/5000000000 : ℝ)*X 2 1+(-266319063/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((893269669/2000000000 : ℝ)*X 0 0+(430772251/1000000000 : ℝ)*X 0 1+(538465243/1250000000 : ℝ)*X 0 2+(893269669/2000000000 : ℝ)*X 1 0+(430772251/1000000000 : ℝ)*X 1 1+(538465243/1250000000 : ℝ)*X 1 2+(893269669/2000000000 : ℝ)*X 2 0+(430772251/1000000000 : ℝ)*X 2 1+(538465243/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-568846157/2500000000 : ℝ)*X 0 0+(1056323489/2000000000 : ℝ)*X 0 1+(5281617453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362774497/10000000000 : ℝ)*X 1 0+(-216769481/1000000000 : ℝ)*X 1 1+(5281617431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681387293/5000000000 : ℝ)*X 2 0+(5281617441/10000000000 : ℝ)*X 2 1+(-2167694677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((850338681/2000000000 : ℝ)*X 0 0+(4415029083/10000000000 : ℝ)*X 0 1+(220751461/500000000 : ℝ)*X 0 2+(850338681/2000000000 : ℝ)*X 1 0+(4415029083/10000000000 : ℝ)*X 1 1+(220751461/500000000 : ℝ)*X 1 2+(850338681/2000000000 : ℝ)*X 2 0+(4415029083/10000000000 : ℝ)*X 2 1+(220751461/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2222511003/10000000000 : ℝ)*X 0 0+(652190563/1250000000 : ℝ)*X 0 1+(5385360593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289541067/10000000000 : ℝ)*X 1 0+(-2126691293/10000000000 : ℝ)*X 1 1+(134634009/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((330596313/625000000 : ℝ)*X 2 0+(5385360123/10000000000 : ℝ)*X 2 1+(-531672923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2243996833/5000000000 : ℝ)*X 0 0+(214837951/500000000 : ℝ)*X 0 1+(4296759019/10000000000 : ℝ)*X 0 2+(2243996833/5000000000 : ℝ)*X 1 0+(214837951/500000000 : ℝ)*X 1 1+(4296759019/10000000000 : ℝ)*X 1 2+(2243996833/5000000000 : ℝ)*X 2 0+(214837951/500000000 : ℝ)*X 2 1+(4296759019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2075919143/10000000000 : ℝ)*X 0 0+(5438591719/10000000000 : ℝ)*X 0 1+(1318390337/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073691731/2000000000 : ℝ)*X 1 0+(-2170817163/10000000000 : ℝ)*X 1 1+(1054712269/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368458653/10000000000 : ℝ)*X 2 0+(2636780999/5000000000 : ℝ)*X 2 1+(-1085408147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2116545761/5000000000 : ℝ)*X 0 0+(2212103867/5000000000 : ℝ)*X 0 1+(4424207609/10000000000 : ℝ)*X 0 2+(2116545761/5000000000 : ℝ)*X 1 0+(2212103867/5000000000 : ℝ)*X 1 1+(4424207609/10000000000 : ℝ)*X 1 2+(2116545761/5000000000 : ℝ)*X 2 0+(2212103867/5000000000 : ℝ)*X 2 1+(4424207609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15559/25000 : ℝ) ≤ (-69157277107005328735097940964503/111125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12312121/25000000000000 : ℝ)*(upper0) + (12416917/100000000000000 : ℝ)*(lower1) + (620311/800000000000 : ℝ)*(lower2) + (575119/2500000000000 : ℝ)*(lower3) + (2547243/50000000000000 : ℝ)*(upper5) + (988203646176879/25000000000000 : ℝ)*(major0) + (988203646176879/25000000000000 : ℝ)*(major1) + (988203646176879/25000000000000 : ℝ)*(major2) + (112799883/100000000000000 : ℝ)*(sp1) + (5295289804004463/100000000000000 : ℝ)*(sp4) + (264764484560229/5000000000000 : ℝ)*(sp5) + (5295237620798689/100000000000000 : ℝ)*(sp6) + (657770988867223/25000000000000 : ℝ)*(sp7) + (26091602887/50000000000000 : ℝ)*(sp14) + (657770988867223/25000000000000 : ℝ)*(f.failure) + (5295289804004463/100000000000000 : ℝ)*(f.sum) + (6818772967541/1111250000000000000000000000 : ℝ)*base65 + (887550513702771501/222250000000000000000000000000000 : ℝ)*base67 + (12505297237649771501/222250000000000000000000000000000 : ℝ)*base69 + (189514431254978499/222250000000000000000000000000000 : ℝ)*base72 + (84722367539899/4445000000000000000000000000 : ℝ)*base73 + (3393427957279728499/222250000000000000000000000000000 : ℝ)*base76 + (1746281316081521501/222250000000000000000000000000000 : ℝ)*base77 + (5084907503084271501/222250000000000000000000000000000 : ℝ)*base79 + (146634002158089/4445000000000000000000000000 : ℝ)*base81 + (23876501/2500000000000000000000 : ℝ)*base90 + (23876501/2500000000000000000000 : ℝ)*base92 + (23876501/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59329/100000 : ℝ) ≤ (263727498340183047018435794031063/444500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46426801/50000000000000 : ℝ)*(upper0) + (4058981/12500000000000 : ℝ)*(upper3) + (57924173/12500000000000 : ℝ)*(upper4) + (4017591443721041/100000000000000 : ℝ)*(major0) + (4017591443721041/100000000000000 : ℝ)*(major1) + (4017591443721041/100000000000000 : ℝ)*(major2) + (53412004850507/1000000000000 : ℝ)*(sp0) + (2670497215047131/50000000000000 : ℝ)*(sp1) + (5340939841553373/100000000000000 : ℝ)*(sp2) + (2674186560674193/100000000000000 : ℝ)*(sp3) + (1098785017/25000000000000 : ℝ)*(sp8) + (105225048253/50000000000000 : ℝ)*(sp9) + (53007727479/20000000000000 : ℝ)*(sp10) + (358908447/2500000000000 : ℝ)*(sp11) + (2674200917012073/100000000000000 : ℝ)*(f.failure) + (333825305011923/6250000000000 : ℝ)*(f.sum) + (6606258236607/2222500000000000000000000000 : ℝ)*base65 + (1389719250886077021/889000000000000000000000000000000 : ℝ)*base68 + (3360366405387922979/889000000000000000000000000000000 : ℝ)*base69 + (6229289552848922979/889000000000000000000000000000000 : ℝ)*base71 + (44920318240691/4445000000000000000000000000 : ℝ)*base74 + (7017125372017922979/889000000000000000000000000000000 : ℝ)*base75 + (3230927009707922979/889000000000000000000000000000000 : ℝ)*base77 + (28286203848589077021/889000000000000000000000000000000 : ℝ)*base80 + (8490995605759/4445000000000000000000000000 : ℝ)*base81 + (10726549/10000000000000000000000 : ℝ)*base89 + (10726549/10000000000000000000000 : ℝ)*base91 + (10726549/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79927/100000 : ℝ) ≤ (444106546816025686382587737/555625000000000000000000000 : ℝ) := by norm_num
    linear_combination (249312771/100000000000000 : ℝ)*(upper0) + (16719877/12500000000000 : ℝ)*(upper1) + (87848389/100000000000000 : ℝ)*(upper2) + (323604061/100000000000000 : ℝ)*(lower5) + (2242552996635953/50000000000000 : ℝ)*(major0) + (2242552996635953/50000000000000 : ℝ)*(major1) + (2242552996635953/50000000000000 : ℝ)*(major2) + (38818672891/50000000000000 : ℝ)*(sp1) + (418345947/4000000000000 : ℝ)*(sp3) + (3840615143/50000000000000 : ℝ)*(sp4) + (5958171929882623/100000000000000 : ℝ)*(sp8) + (744762746720891/12500000000000 : ℝ)*(sp9) + (5958179611112909/100000000000000 : ℝ)*(sp10) + (93293089198627/3125000000000 : ℝ)*(sp11) + (2985389313004739/100000000000000 : ℝ)*(f.failure) + (5958179611112909/100000000000000 : ℝ)*(f.sum) + (417856098831/277812500000000000000000000 : ℝ)*base66 + (181340216655231293/444500000000000000000000000000000 : ℝ)*base68 + (2485651950810268707/444500000000000000000000000000000 : ℝ)*base69 + (1372329473038731293/444500000000000000000000000000000 : ℝ)*base72 + (31556005443343/2222500000000000000000000000 : ℝ)*base74 + (2916549336396231293/444500000000000000000000000000000 : ℝ)*base76 + (2084653673179268707/444500000000000000000000000000000 : ℝ)*base77 + (2115438158092268707/444500000000000000000000000000000 : ℝ)*base79 + (6930351319083/2222500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (33674407/10000000000000000000000 : ℝ)*base89 + (33674407/10000000000000000000000 : ℝ)*base91 + (33674407/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83211/100000 : ℝ) ≤ (-73972792100538425883429746260461/88900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3219701/1000000000000 : ℝ)*(lower0) + (40493849/25000000000000 : ℝ)*(lower2) + (17659849/25000000000000 : ℝ)*(upper3) + (6335433/800000000000 : ℝ)*(upper5) + (904049795792427/20000000000000 : ℝ)*(major0) + (904049795792427/20000000000000 : ℝ)*(major1) + (904049795792427/20000000000000 : ℝ)*(major2) + (7771279531/50000000000000 : ℝ)*(sp0) + (71772849561/25000000000000 : ℝ)*(sp5) + (28619859429/25000000000000 : ℝ)*(sp7) + (3029718727938261/50000000000000 : ℝ)*(sp12) + (302958295351867/5000000000000 : ℝ)*(sp13) + (23669738275139/390625000000 : ℝ)*(sp14) + (376083351255927/12500000000000 : ℝ)*(sp15) + (752195322371283/25000000000000 : ℝ)*(f.failure) + (23669738275139/390625000000 : ℝ)*(f.sum) + (3622170002621/889000000000000000000000000 : ℝ)*base65 + (801206622747653487/177800000000000000000000000000000 : ℝ)*base68 + (1160999983474453487/177800000000000000000000000000000 : ℝ)*base70 + (1526262750650746513/177800000000000000000000000000000 : ℝ)*base71 + (1449664830781/177800000000000000000000000 : ℝ)*base73 + (559568119487653487/177800000000000000000000000000000 : ℝ)*base76 + (1159470705775546513/177800000000000000000000000000000 : ℝ)*base77 + (686123185960453487/177800000000000000000000000000000 : ℝ)*base80 + (1184920497479/889000000000000000000000000 : ℝ)*base82 + (8411721/2500000000000000000000 : ℝ)*base90 + (8411721/2500000000000000000000 : ℝ)*base92 + (8411721/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1181_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59329/100000 : ℝ) else (79927/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83211/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1181_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1181_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59329/100000 : ℝ) else (79927/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83211/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1181_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59329/100000 : ℝ) else (79927/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83211/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1181_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
