-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1075_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:13:51.608726+00:00
-- url     : https://prove2.me/submissions/bfdaf94d-b477-45af-9e81-975e2ed523ab

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
theorem support_rectangle_w1075_s9_0 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672476139/5000000000 : ℝ)*x 0 + (-2265062409/10000000000 : ℝ)*x 1 + (5264641887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672476139/5000000000 : ℝ)^2067 ≤ (679495401009/1562500000000 : ℝ)^1555 := by
    have hnat : (2672476139 : ℕ)^2067*1562500000000^1555 ≤ 679495401009^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672476139 5000000000 679495401009 1562500000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265062409/10000000000 : ℝ)^2067 ≤ (13891002193259/100000000000000 : ℝ)^1555 := by
    have hnat : (2265062409 : ℕ)^2067*100000000000000^1555 ≤ 13891002193259^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265062409 10000000000 13891002193259 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264641887/10000000000 : ℝ)^2067 ≤ (1065532303403/2500000000000 : ℝ)^1555 := by
    have hnat : (5264641887 : ℕ)^2067*2500000000000^1555 ≤ 1065532303403^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264641887 10000000000 1065532303403 2500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672476139/5000000000 : ℝ), (-2265062409/10000000000 : ℝ), (5264641887/10000000000 : ℝ)] ![(679495401009/1562500000000 : ℝ), (13891002193259/100000000000000 : ℝ), (1065532303403/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672476139/5000000000 : ℝ)|^2067 ≤ (679495401009/1562500000000 : ℝ)^1555
        have hw : |(2672476139/5000000000 : ℝ)|=(2672476139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2265062409/10000000000 : ℝ)|^2067 ≤ (13891002193259/100000000000000 : ℝ)^1555
        have hw : |(-2265062409/10000000000 : ℝ)|=(2265062409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264641887/10000000000 : ℝ)|^2067 ≤ (1065532303403/2500000000000 : ℝ)^1555
        have hw : |(5264641887/10000000000 : ℝ)|=(5264641887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s9_1 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199349229/10000000000 : ℝ)*x 0 + (1316241597/2500000000 : ℝ)*x 1 + (1078769893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199349229/10000000000 : ℝ)^2067 ≤ (6678942281359/50000000000000 : ℝ)^1555 := by
    have hnat : (2199349229 : ℕ)^2067*50000000000000^1555 ≤ 6678942281359^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199349229 10000000000 6678942281359 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316241597/2500000000 : ℝ)^2067 ≤ (42624784249267/100000000000000 : ℝ)^1555 := by
    have hnat : (1316241597 : ℕ)^2067*100000000000000^1555 ≤ 42624784249267^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316241597 2500000000 42624784249267 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078769893/2000000000 : ℝ)^2067 ≤ (44017331160997/100000000000000 : ℝ)^1555 := by
    have hnat : (1078769893 : ℕ)^2067*100000000000000^1555 ≤ 44017331160997^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078769893 2000000000 44017331160997 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199349229/10000000000 : ℝ), (1316241597/2500000000 : ℝ), (1078769893/2000000000 : ℝ)] ![(6678942281359/50000000000000 : ℝ), (42624784249267/100000000000000 : ℝ), (44017331160997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199349229/10000000000 : ℝ)|^2067 ≤ (6678942281359/50000000000000 : ℝ)^1555
        have hw : |(-2199349229/10000000000 : ℝ)|=(2199349229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316241597/2500000000 : ℝ)|^2067 ≤ (42624784249267/100000000000000 : ℝ)^1555
        have hw : |(1316241597/2500000000 : ℝ)|=(1316241597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078769893/2000000000 : ℝ)|^2067 ≤ (44017331160997/100000000000000 : ℝ)^1555
        have hw : |(1078769893/2000000000 : ℝ)|=(1078769893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s9_2 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (664037753/1250000000 : ℝ)*x 0 + (-266981853/1250000000 : ℝ)*x 1 + (5393849519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664037753/1250000000 : ℝ)^2067 ≤ (43134943711041/100000000000000 : ℝ)^1555 := by
    have hnat : (664037753 : ℕ)^2067*100000000000000^1555 ≤ 43134943711041^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664037753 1250000000 43134943711041 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266981853/1250000000 : ℝ)^2067 ≤ (802982782599/6250000000000 : ℝ)^1555 := by
    have hnat : (266981853 : ℕ)^2067*6250000000000^1555 ≤ 802982782599^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266981853 1250000000 802982782599 6250000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393849519/10000000000 : ℝ)^2067 ≤ (44017331746769/100000000000000 : ℝ)^1555 := by
    have hnat : (5393849519 : ℕ)^2067*100000000000000^1555 ≤ 44017331746769^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393849519 10000000000 44017331746769 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664037753/1250000000 : ℝ), (-266981853/1250000000 : ℝ), (5393849519/10000000000 : ℝ)] ![(43134943711041/100000000000000 : ℝ), (802982782599/6250000000000 : ℝ), (44017331746769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664037753/1250000000 : ℝ)|^2067 ≤ (43134943711041/100000000000000 : ℝ)^1555
        have hw : |(664037753/1250000000 : ℝ)|=(664037753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266981853/1250000000 : ℝ)|^2067 ≤ (802982782599/6250000000000 : ℝ)^1555
        have hw : |(-266981853/1250000000 : ℝ)|=(266981853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393849519/10000000000 : ℝ)|^2067 ≤ (44017331746769/100000000000000 : ℝ)^1555
        have hw : |(5393849519/10000000000 : ℝ)|=(5393849519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s9_3 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062460391/2000000000 : ℝ)*x 0 + (674231197/1250000000 : ℝ)*x 1 + (-2135854841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062460391/2000000000 : ℝ)^2067 ≤ (43134942966299/100000000000000 : ℝ)^1555 := by
    have hnat : (1062460391 : ℕ)^2067*100000000000000^1555 ≤ 43134942966299^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062460391 2000000000 43134942966299 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674231197/1250000000 : ℝ)^2067 ≤ (11004333091271/25000000000000 : ℝ)^1555 := by
    have hnat : (674231197 : ℕ)^2067*25000000000000^1555 ≤ 11004333091271^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674231197 1250000000 11004333091271 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135854841/10000000000 : ℝ)^2067 ≤ (6423862328757/50000000000000 : ℝ)^1555 := by
    have hnat : (2135854841 : ℕ)^2067*50000000000000^1555 ≤ 6423862328757^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135854841 10000000000 6423862328757 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062460391/2000000000 : ℝ), (674231197/1250000000 : ℝ), (-2135854841/10000000000 : ℝ)] ![(43134942966299/100000000000000 : ℝ), (11004333091271/25000000000000 : ℝ), (6423862328757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062460391/2000000000 : ℝ)|^2067 ≤ (43134942966299/100000000000000 : ℝ)^1555
        have hw : |(1062460391/2000000000 : ℝ)|=(1062460391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674231197/1250000000 : ℝ)|^2067 ≤ (11004333091271/25000000000000 : ℝ)^1555
        have hw : |(674231197/1250000000 : ℝ)|=(674231197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135854841/10000000000 : ℝ)|^2067 ≤ (6423862328757/50000000000000 : ℝ)^1555
        have hw : |(-2135854841/10000000000 : ℝ)|=(2135854841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s9_4 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4374210659/10000000000 : ℝ)*x 0 + (2251296257/5000000000 : ℝ)*x 1 + (2124774103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374210659/10000000000 : ℝ)^2067 ≤ (16658357213223/50000000000000 : ℝ)^1555 := by
    have hnat : (4374210659 : ℕ)^2067*50000000000000^1555 ≤ 16658357213223^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374210659 10000000000 16658357213223 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251296257/5000000000 : ℝ)^2067 ≤ (6924550631169/20000000000000 : ℝ)^1555 := by
    have hnat : (2251296257 : ℕ)^2067*20000000000000^1555 ≤ 6924550631169^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251296257 5000000000 6924550631169 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124774103/5000000000 : ℝ)^2067 ≤ (32060532403179/100000000000000 : ℝ)^1555 := by
    have hnat : (2124774103 : ℕ)^2067*100000000000000^1555 ≤ 32060532403179^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124774103 5000000000 32060532403179 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374210659/10000000000 : ℝ), (2251296257/5000000000 : ℝ), (2124774103/5000000000 : ℝ)] ![(16658357213223/50000000000000 : ℝ), (6924550631169/20000000000000 : ℝ), (32060532403179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374210659/10000000000 : ℝ)|^2067 ≤ (16658357213223/50000000000000 : ℝ)^1555
        have hw : |(4374210659/10000000000 : ℝ)|=(4374210659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251296257/5000000000 : ℝ)|^2067 ≤ (6924550631169/20000000000000 : ℝ)^1555
        have hw : |(2251296257/5000000000 : ℝ)|=(2251296257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124774103/5000000000 : ℝ)|^2067 ≤ (32060532403179/100000000000000 : ℝ)^1555
        have hw : |(2124774103/5000000000 : ℝ)|=(2124774103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1075_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (352/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1751/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (352/3125 : ℝ) ^ (8267/2048 : ℝ) ≤ (1857601390703937/12500000000000000000 : ℝ) := by
    have hpowers : (352/3125 : ℝ)^8267 ≤ (1857601390703937/12500000000000000000 : ℝ)^2048 := by
      have hnat : (352 : ℕ)^8267*12500000000000000000^2048 ≤ 1857601390703937^2048*3125^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        352 3125 1857601390703937 12500000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (352/3125 : ℝ)) (X := (1857601390703937/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14009/100000 : ℝ) ^ (8267/2048 : ℝ) ≤ (8960021370508539/25000000000000000000 : ℝ) := by
    have hpowers : (14009/100000 : ℝ)^8267 ≤ (8960021370508539/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14009 : ℕ)^8267*25000000000000000000^2048 ≤ 8960021370508539^2048*100000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14009 100000 8960021370508539 25000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14009/100000 : ℝ)) (X := (8960021370508539/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251857601390703937/6250000000000000000 : ℝ) ≤ (5000368108616891/5000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (6251857601390703937/6250000000000000000 : ℝ)^2048 ≤ (5000368108616891/5000000000000000 : ℝ)^8267 := by
      have hnat : (6251857601390703937 : ℕ)^2048*5000000000000000^8267 ≤ 5000368108616891^8267*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251857601390703937 6250000000000000000 5000368108616891 5000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000368108616891/5000000000000000 : ℝ)) (X := (6251857601390703937/6250000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012675224151916413/25000000000000000000 : ℝ) ≤ (10001255783722653/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (25012675224151916413/25000000000000000000 : ℝ)^2048 ≤ (10001255783722653/10000000000000000 : ℝ)^8267 := by
      have hnat : (25012675224151916413 : ℕ)^2048*10000000000000000^8267 ≤ 10001255783722653^8267*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012675224151916413 25000000000000000000 10001255783722653 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001255783722653/10000000000000000 : ℝ)) (X := (25012675224151916413/25000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508960021370508539/12500000000000000000 : ℝ) ≤ (2500443837552881/2500000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (12508960021370508539/12500000000000000000 : ℝ)^2048 ≤ (2500443837552881/2500000000000000 : ℝ)^8267 := by
      have hnat : (12508960021370508539 : ℕ)^2048*2500000000000000^8267 ≤ 2500443837552881^8267*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508960021370508539 12500000000000000000 2500443837552881 2500000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500443837552881/2500000000000000 : ℝ)) (X := (12508960021370508539/12500000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1857601390703937/12500000000000000000 : ℝ) ≤ ((13720158061222722851/13725000000000000000 : ℝ)+2*(519566488871/274500000000000 : ℝ)*(352/3125 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (13720158061222722851/13725000000000000000 : ℝ)+2*(519566488871/274500000000000 : ℝ)*(352/3125 : ℝ)=(5000368108616891/5000000000000000 : ℝ) by norm_num, show 1+2*(1857601390703937/12500000000000000000 : ℝ)=(6251857601390703937/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8960021370508539/25000000000000000000 : ℝ)+(1857601390703937/12500000000000000000 : ℝ) ≤ ((13720158061222722851/13725000000000000000 : ℝ)+(519566488871/274500000000000 : ℝ)*((14009/100000 : ℝ)+(352/3125 : ℝ)))^(8267/2048 : ℝ) := by
    rw [show (13720158061222722851/13725000000000000000 : ℝ)+(519566488871/274500000000000 : ℝ)*((14009/100000 : ℝ)+(352/3125 : ℝ))=(10001255783722653/10000000000000000 : ℝ) by norm_num, show 1+(8960021370508539/25000000000000000000 : ℝ)+(1857601390703937/12500000000000000000 : ℝ)=(25012675224151916413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8960021370508539/25000000000000000000 : ℝ) ≤ ((13720158061222722851/13725000000000000000 : ℝ)+2*(519566488871/274500000000000 : ℝ)*(14009/100000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (13720158061222722851/13725000000000000000 : ℝ)+2*(519566488871/274500000000000 : ℝ)*(14009/100000 : ℝ)=(2500443837552881/2500000000000000 : ℝ) by norm_num, show 1+2*(8960021370508539/25000000000000000000 : ℝ)=(12508960021370508539/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13720158061222722851/13725000000000000000 : ℝ)*(X 1 0+X 2 0)+(519566488871/274500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (13720158061222722851/13725000000000000000 : ℝ)) (alpha := (519566488871/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13720158061222722851/13725000000000000000 : ℝ)*(X 0 1+X 2 1)+(519566488871/274500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (13720158061222722851/13725000000000000000 : ℝ)) (alpha := (519566488871/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13720158061222722851/13725000000000000000 : ℝ)*(X 0 2+X 1 2)+(519566488871/274500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (13720158061222722851/13725000000000000000 : ℝ)) (alpha := (519566488871/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672476139/5000000000 : ℝ)*X 1 0+(-2265062409/10000000000 : ℝ)*X 1 1+(5264641887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2199349229/10000000000 : ℝ)*X 0 0+(1316241597/2500000000 : ℝ)*X 0 1+(1078769893/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((664037753/1250000000 : ℝ)*X 1 0+(-266981853/1250000000 : ℝ)*X 1 1+(5393849519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062460391/2000000000 : ℝ)*X 2 0+(674231197/1250000000 : ℝ)*X 2 1+(-2135854841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4374210659/10000000000 : ℝ)*X 0 0+(2251296257/5000000000 : ℝ)*X 0 1+(2124774103/5000000000 : ℝ)*X 0 2+(4374210659/10000000000 : ℝ)*X 1 0+(2251296257/5000000000 : ℝ)*X 1 1+(2124774103/5000000000 : ℝ)*X 1 2+(4374210659/10000000000 : ℝ)*X 2 0+(2251296257/5000000000 : ℝ)*X 2 1+(2124774103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80774667577031607473339191/15250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (586984077/50000000000000 : ℝ)*(base19) + (1105890139/100000000000000 : ℝ)*(base23) + (6759057/1562500000000 : ℝ)*(lower1) + (147787549/100000000000000 : ℝ)*(upper3) + (17947299/100000000000000 : ℝ)*(lower4) + (133452113/100000000000000 : ℝ)*(upper5) + (1171079442602659/20000000000000 : ℝ)*(major0) + (1171079442602659/20000000000000 : ℝ)*(major1) + (1171079442602659/20000000000000 : ℝ)*(major2) + (22042513/12500000000000 : ℝ)*(sp0) + (3879467353898689/50000000000000 : ℝ)*(sp1) + (48493333484307/625000000000 : ℝ)*(sp2) + (7758933601907239/100000000000000 : ℝ)*(sp3) + (493982442709069/12500000000000 : ℝ)*(sp4) + (493982442709069/12500000000000 : ℝ)*(f.failure) + (3879467353898689/50000000000000 : ℝ)*(f.sum) + (1146561507481/2745000000000000000000000000 : ℝ)*base66 + (408639030540901201/30500000000000000000000000000000 : ℝ)*base67 + (293601018795901201/30500000000000000000000000000000 : ℝ)*base69 + (27390214916901201/30500000000000000000000000000000 : ℝ)*base71 + (4912152798451/2745000000000000000000000000 : ℝ)*base74 + (471038832676901201/30500000000000000000000000000000 : ℝ)*base75 + (53107313100401201/30500000000000000000000000000000 : ℝ)*base77 + (1104437055540901201/30500000000000000000000000000000 : ℝ)*base79 + (3228139491049/686250000000000000000000000 : ℝ)*base82 + (2838581/1250000000000000000000 : ℝ)*base90 + (2838581/1250000000000000000000 : ℝ)*base92 + (2838581/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1075_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1075_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1075_box_0 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-41403891/200000000 : ℝ)*x 0 + (268862261/500000000 : ℝ)*x 1 + (672155629/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41403891/200000000 : ℝ)^2067 ≤ (6162695251941/50000000000000 : ℝ)^1555 := by
    have hnat : (41403891 : ℕ)^2067*50000000000000^1555 ≤ 6162695251941^1555*200000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41403891 200000000 6162695251941 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268862261/500000000 : ℝ)^2067 ≤ (21918652877937/50000000000000 : ℝ)^1555 := by
    have hnat : (268862261 : ℕ)^2067*50000000000000^1555 ≤ 21918652877937^1555*500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268862261 500000000 21918652877937 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672155629/1250000000 : ℝ)^2067 ≤ (10959325929647/25000000000000 : ℝ)^1555 := by
    have hnat : (672155629 : ℕ)^2067*25000000000000^1555 ≤ 10959325929647^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672155629 1250000000 10959325929647 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41403891/200000000 : ℝ), (268862261/500000000 : ℝ), (672155629/1250000000 : ℝ)] ![(6162695251941/50000000000000 : ℝ), (21918652877937/50000000000000 : ℝ), (10959325929647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41403891/200000000 : ℝ)|^2067 ≤ (6162695251941/50000000000000 : ℝ)^1555
        have hw : |(-41403891/200000000 : ℝ)|=(41403891/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268862261/500000000 : ℝ)|^2067 ≤ (21918652877937/50000000000000 : ℝ)^1555
        have hw : |(268862261/500000000 : ℝ)|=(268862261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672155629/1250000000 : ℝ)|^2067 ≤ (10959325929647/25000000000000 : ℝ)^1555
        have hw : |(672155629/1250000000 : ℝ)|=(672155629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_1 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647651383/5000000000 : ℝ)*x 0 + (-545286831/2500000000 : ℝ)*x 1 + (2688622517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647651383/5000000000 : ℝ)^2067 ≤ (42951561371317/100000000000000 : ℝ)^1555 := by
    have hnat : (2647651383 : ℕ)^2067*100000000000000^1555 ≤ 42951561371317^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647651383 5000000000 42951561371317 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545286831/2500000000 : ℝ)^2067 ≤ (2642226974493/20000000000000 : ℝ)^1555 := by
    have hnat : (545286831 : ℕ)^2067*20000000000000^1555 ≤ 2642226974493^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545286831 2500000000 2642226974493 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688622517/5000000000 : ℝ)^2067 ≤ (21918651870131/50000000000000 : ℝ)^1555 := by
    have hnat : (2688622517 : ℕ)^2067*50000000000000^1555 ≤ 21918651870131^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688622517 5000000000 21918651870131 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647651383/5000000000 : ℝ), (-545286831/2500000000 : ℝ), (2688622517/5000000000 : ℝ)] ![(42951561371317/100000000000000 : ℝ), (2642226974493/20000000000000 : ℝ), (21918651870131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647651383/5000000000 : ℝ)|^2067 ≤ (42951561371317/100000000000000 : ℝ)^1555
        have hw : |(2647651383/5000000000 : ℝ)|=(2647651383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545286831/2500000000 : ℝ)|^2067 ≤ (2642226974493/20000000000000 : ℝ)^1555
        have hw : |(-545286831/2500000000 : ℝ)|=(545286831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688622517/5000000000 : ℝ)|^2067 ≤ (21918651870131/50000000000000 : ℝ)^1555
        have hw : |(2688622517/5000000000 : ℝ)|=(2688622517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_2 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647651441/5000000000 : ℝ)*x 0 + (1344311237/2500000000 : ℝ)*x 1 + (-545286821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647651441/5000000000 : ℝ)^2067 ≤ (21475781311013/50000000000000 : ℝ)^1555 := by
    have hnat : (2647651441 : ℕ)^2067*50000000000000^1555 ≤ 21475781311013^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647651441 5000000000 21475781311013 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344311237/2500000000 : ℝ)^2067 ≤ (5479662851039/12500000000000 : ℝ)^1555 := by
    have hnat : (1344311237 : ℕ)^2067*12500000000000^1555 ≤ 5479662851039^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344311237 2500000000 5479662851039 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545286821/2500000000 : ℝ)^2067 ≤ (13211134550413/100000000000000 : ℝ)^1555 := by
    have hnat : (545286821 : ℕ)^2067*100000000000000^1555 ≤ 13211134550413^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545286821 2500000000 13211134550413 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647651441/5000000000 : ℝ), (1344311237/2500000000 : ℝ), (-545286821/2500000000 : ℝ)] ![(21475781311013/50000000000000 : ℝ), (5479662851039/12500000000000 : ℝ), (13211134550413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647651441/5000000000 : ℝ)|^2067 ≤ (21475781311013/50000000000000 : ℝ)^1555
        have hw : |(2647651441/5000000000 : ℝ)|=(2647651441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344311237/2500000000 : ℝ)|^2067 ≤ (5479662851039/12500000000000 : ℝ)^1555
        have hw : |(1344311237/2500000000 : ℝ)|=(1344311237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545286821/2500000000 : ℝ)|^2067 ≤ (13211134550413/100000000000000 : ℝ)^1555
        have hw : |(-545286821/2500000000 : ℝ)|=(545286821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_3 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4482485641/10000000000 : ℝ)*x 0 + (4322213853/10000000000 : ℝ)*x 1 + (2161106993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482485641/10000000000 : ℝ)^2067 ≤ (430217308071/1250000000000 : ℝ)^1555 := by
    have hnat : (4482485641 : ℕ)^2067*1250000000000^1555 ≤ 430217308071^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482485641 10000000000 430217308071 1250000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4322213853/10000000000 : ℝ)^2067 ≤ (32791306997747/100000000000000 : ℝ)^1555 := by
    have hnat : (4322213853 : ℕ)^2067*100000000000000^1555 ≤ 32791306997747^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322213853 10000000000 32791306997747 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161106993/5000000000 : ℝ)^2067 ≤ (32791308339011/100000000000000 : ℝ)^1555 := by
    have hnat : (2161106993 : ℕ)^2067*100000000000000^1555 ≤ 32791308339011^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161106993 5000000000 32791308339011 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482485641/10000000000 : ℝ), (4322213853/10000000000 : ℝ), (2161106993/5000000000 : ℝ)] ![(430217308071/1250000000000 : ℝ), (32791306997747/100000000000000 : ℝ), (32791308339011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482485641/10000000000 : ℝ)|^2067 ≤ (430217308071/1250000000000 : ℝ)^1555
        have hw : |(4482485641/10000000000 : ℝ)|=(4482485641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4322213853/10000000000 : ℝ)|^2067 ≤ (32791306997747/100000000000000 : ℝ)^1555
        have hw : |(4322213853/10000000000 : ℝ)|=(4322213853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2161106993/5000000000 : ℝ)|^2067 ≤ (32791308339011/100000000000000 : ℝ)^1555
        have hw : |(2161106993/5000000000 : ℝ)|=(2161106993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_4 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1164943149/5000000000 : ℝ)*x 0 + (5280222467/10000000000 : ℝ)*x 1 + (2640111033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1164943149/5000000000 : ℝ)^2067 ≤ (14421919756677/100000000000000 : ℝ)^1555 := by
    have hnat : (1164943149 : ℕ)^2067*100000000000000^1555 ≤ 14421919756677^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164943149 5000000000 14421919756677 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280222467/10000000000 : ℝ)^2067 ≤ (10697260568547/25000000000000 : ℝ)^1555 := by
    have hnat : (5280222467 : ℕ)^2067*25000000000000^1555 ≤ 10697260568547^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280222467 10000000000 10697260568547 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640111033/5000000000 : ℝ)^2067 ≤ (1711561518187/4000000000000 : ℝ)^1555 := by
    have hnat : (2640111033 : ℕ)^2067*4000000000000^1555 ≤ 1711561518187^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640111033 5000000000 1711561518187 4000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1164943149/5000000000 : ℝ), (5280222467/10000000000 : ℝ), (2640111033/5000000000 : ℝ)] ![(14421919756677/100000000000000 : ℝ), (10697260568547/25000000000000 : ℝ), (1711561518187/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1164943149/5000000000 : ℝ)|^2067 ≤ (14421919756677/100000000000000 : ℝ)^1555
        have hw : |(-1164943149/5000000000 : ℝ)|=(1164943149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280222467/10000000000 : ℝ)|^2067 ≤ (10697260568547/25000000000000 : ℝ)^1555
        have hw : |(5280222467/10000000000 : ℝ)|=(5280222467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640111033/5000000000 : ℝ)|^2067 ≤ (1711561518187/4000000000000 : ℝ)^1555
        have hw : |(2640111033/5000000000 : ℝ)|=(2640111033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_5 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1072790681/2000000000 : ℝ)*x 0 + (-44382153/200000000 : ℝ)*x 1 + (5280222017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072790681/2000000000 : ℝ)^2067 ≤ (43693325972257/100000000000000 : ℝ)^1555 := by
    have hnat : (1072790681 : ℕ)^2067*100000000000000^1555 ≤ 43693325972257^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072790681 2000000000 43693325972257 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44382153/200000000 : ℝ)^2067 ≤ (1689704573447/12500000000000 : ℝ)^1555 := by
    have hnat : (44382153 : ℕ)^2067*12500000000000^1555 ≤ 1689704573447^1555*200000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44382153 200000000 1689704573447 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280222017/10000000000 : ℝ)^2067 ≤ (21394518713427/50000000000000 : ℝ)^1555 := by
    have hnat : (5280222017 : ℕ)^2067*50000000000000^1555 ≤ 21394518713427^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280222017 10000000000 21394518713427 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072790681/2000000000 : ℝ), (-44382153/200000000 : ℝ), (5280222017/10000000000 : ℝ)] ![(43693325972257/100000000000000 : ℝ), (1689704573447/12500000000000 : ℝ), (21394518713427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072790681/2000000000 : ℝ)|^2067 ≤ (43693325972257/100000000000000 : ℝ)^1555
        have hw : |(1072790681/2000000000 : ℝ)|=(1072790681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44382153/200000000 : ℝ)|^2067 ≤ (1689704573447/12500000000000 : ℝ)^1555
        have hw : |(-44382153/200000000 : ℝ)|=(44382153/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280222017/10000000000 : ℝ)|^2067 ≤ (21394518713427/50000000000000 : ℝ)^1555
        have hw : |(5280222017/10000000000 : ℝ)|=(5280222017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_6 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (670494123/1250000000 : ℝ)*x 0 + (5280222543/10000000000 : ℝ)*x 1 + (-2219107513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670494123/1250000000 : ℝ)^2067 ≤ (21846660706877/50000000000000 : ℝ)^1555 := by
    have hnat : (670494123 : ℕ)^2067*50000000000000^1555 ≤ 21846660706877^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670494123 1250000000 21846660706877 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280222543/10000000000 : ℝ)^2067 ≤ (42789043092849/100000000000000 : ℝ)^1555 := by
    have hnat : (5280222543 : ℕ)^2067*100000000000000^1555 ≤ 42789043092849^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280222543 10000000000 42789043092849 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219107513/10000000000 : ℝ)^2067 ≤ (6758817739133/50000000000000 : ℝ)^1555 := by
    have hnat : (2219107513 : ℕ)^2067*50000000000000^1555 ≤ 6758817739133^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219107513 10000000000 6758817739133 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670494123/1250000000 : ℝ), (5280222543/10000000000 : ℝ), (-2219107513/10000000000 : ℝ)] ![(21846660706877/50000000000000 : ℝ), (42789043092849/100000000000000 : ℝ), (6758817739133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670494123/1250000000 : ℝ)|^2067 ≤ (21846660706877/50000000000000 : ℝ)^1555
        have hw : |(670494123/1250000000 : ℝ)|=(670494123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280222543/10000000000 : ℝ)|^2067 ≤ (42789043092849/100000000000000 : ℝ)^1555
        have hw : |(5280222543/10000000000 : ℝ)|=(5280222543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2219107513/10000000000 : ℝ)|^2067 ≤ (6758817739133/50000000000000 : ℝ)^1555
        have hw : |(-2219107513/10000000000 : ℝ)|=(2219107513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_7 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2132791139/5000000000 : ℝ)*x 0 + (708903/1600000 : ℝ)*x 1 + (4430644677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132791139/5000000000 : ℝ)^2067 ≤ (32221430661343/100000000000000 : ℝ)^1555 := by
    have hnat : (2132791139 : ℕ)^2067*100000000000000^1555 ≤ 32221430661343^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132791139 5000000000 32221430661343 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708903/1600000 : ℝ)^2067 ≤ (33889279948829/100000000000000 : ℝ)^1555 := by
    have hnat : (708903 : ℕ)^2067*100000000000000^1555 ≤ 33889279948829^1555*1600000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708903 1600000 33889279948829 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4430644677/10000000000 : ℝ)^2067 ≤ (6777857874783/20000000000000 : ℝ)^1555 := by
    have hnat : (4430644677 : ℕ)^2067*20000000000000^1555 ≤ 6777857874783^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4430644677 10000000000 6777857874783 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132791139/5000000000 : ℝ), (708903/1600000 : ℝ), (4430644677/10000000000 : ℝ)] ![(32221430661343/100000000000000 : ℝ), (33889279948829/100000000000000 : ℝ), (6777857874783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132791139/5000000000 : ℝ)|^2067 ≤ (32221430661343/100000000000000 : ℝ)^1555
        have hw : |(2132791139/5000000000 : ℝ)|=(2132791139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708903/1600000 : ℝ)|^2067 ≤ (33889279948829/100000000000000 : ℝ)^1555
        have hw : |(708903/1600000 : ℝ)|=(708903/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4430644677/10000000000 : ℝ)|^2067 ≤ (6777857874783/20000000000000 : ℝ)^1555
        have hw : |(4430644677/10000000000 : ℝ)|=(4430644677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_8 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2275662099/10000000000 : ℝ)*x 0 + (1303592129/2500000000 : ℝ)*x 1 + (2693423581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2275662099/10000000000 : ℝ)^2067 ≤ (2795495446269/20000000000000 : ℝ)^1555 := by
    have hnat : (2275662099 : ℕ)^2067*20000000000000^1555 ≤ 2795495446269^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275662099 10000000000 2795495446269 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303592129/2500000000 : ℝ)^2067 ≤ (42081133763327/100000000000000 : ℝ)^1555 := by
    have hnat : (1303592129 : ℕ)^2067*100000000000000^1555 ≤ 42081133763327^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303592129 2500000000 42081133763327 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693423581/5000000000 : ℝ)^2067 ≤ (10985347247327/25000000000000 : ℝ)^1555 := by
    have hnat : (2693423581 : ℕ)^2067*25000000000000^1555 ≤ 10985347247327^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693423581 5000000000 10985347247327 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2275662099/10000000000 : ℝ), (1303592129/2500000000 : ℝ), (2693423581/5000000000 : ℝ)] ![(2795495446269/20000000000000 : ℝ), (42081133763327/100000000000000 : ℝ), (10985347247327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2275662099/10000000000 : ℝ)|^2067 ≤ (2795495446269/20000000000000 : ℝ)^1555
        have hw : |(-2275662099/10000000000 : ℝ)|=(2275662099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303592129/2500000000 : ℝ)|^2067 ≤ (42081133763327/100000000000000 : ℝ)^1555
        have hw : |(1303592129/2500000000 : ℝ)|=(1303592129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693423581/5000000000 : ℝ)|^2067 ≤ (10985347247327/25000000000000 : ℝ)^1555
        have hw : |(2693423581/5000000000 : ℝ)|=(2693423581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_9 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288504917/10000000000 : ℝ)*x 0 + (-2177320153/10000000000 : ℝ)*x 1 + (2693423499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288504917/10000000000 : ℝ)^2067 ≤ (42878282641243/100000000000000 : ℝ)^1555 := by
    have hnat : (5288504917 : ℕ)^2067*100000000000000^1555 ≤ 42878282641243^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288504917 10000000000 42878282641243 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177320153/10000000000 : ℝ)^2067 ≤ (13180330132009/100000000000000 : ℝ)^1555 := by
    have hnat : (2177320153 : ℕ)^2067*100000000000000^1555 ≤ 13180330132009^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177320153 10000000000 13180330132009 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693423499/5000000000 : ℝ)^2067 ≤ (43941387211057/100000000000000 : ℝ)^1555 := by
    have hnat : (2693423499 : ℕ)^2067*100000000000000^1555 ≤ 43941387211057^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693423499 5000000000 43941387211057 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288504917/10000000000 : ℝ), (-2177320153/10000000000 : ℝ), (2693423499/5000000000 : ℝ)] ![(42878282641243/100000000000000 : ℝ), (13180330132009/100000000000000 : ℝ), (43941387211057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288504917/10000000000 : ℝ)|^2067 ≤ (42878282641243/100000000000000 : ℝ)^1555
        have hw : |(5288504917/10000000000 : ℝ)|=(5288504917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177320153/10000000000 : ℝ)|^2067 ≤ (13180330132009/100000000000000 : ℝ)^1555
        have hw : |(-2177320153/10000000000 : ℝ)|=(2177320153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693423499/5000000000 : ℝ)|^2067 ≤ (43941387211057/100000000000000 : ℝ)^1555
        have hw : |(2693423499/5000000000 : ℝ)|=(2693423499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_10 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (264425249/500000000 : ℝ)*x 0 + (5386847129/10000000000 : ℝ)*x 1 + (-544329973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264425249/500000000 : ℝ)^2067 ≤ (2143914166011/5000000000000 : ℝ)^1555 := by
    have hnat : (264425249 : ℕ)^2067*5000000000000^1555 ≤ 2143914166011^1555*500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264425249 500000000 2143914166011 5000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386847129/10000000000 : ℝ)^2067 ≤ (4394138863149/10000000000000 : ℝ)^1555 := by
    have hnat : (5386847129 : ℕ)^2067*10000000000000^1555 ≤ 4394138863149^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386847129 10000000000 4394138863149 10000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544329973/2500000000 : ℝ)^2067 ≤ (6590164015919/50000000000000 : ℝ)^1555 := by
    have hnat : (544329973 : ℕ)^2067*50000000000000^1555 ≤ 6590164015919^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544329973 2500000000 6590164015919 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264425249/500000000 : ℝ), (5386847129/10000000000 : ℝ), (-544329973/2500000000 : ℝ)] ![(2143914166011/5000000000000 : ℝ), (4394138863149/10000000000000 : ℝ), (6590164015919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264425249/500000000 : ℝ)|^2067 ≤ (2143914166011/5000000000000 : ℝ)^1555
        have hw : |(264425249/500000000 : ℝ)|=(264425249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386847129/10000000000 : ℝ)|^2067 ≤ (4394138863149/10000000000000 : ℝ)^1555
        have hw : |(5386847129/10000000000 : ℝ)|=(5386847129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-544329973/2500000000 : ℝ)|^2067 ≤ (6590164015919/50000000000000 : ℝ)^1555
        have hw : |(-544329973/2500000000 : ℝ)|=(544329973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_11 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4503678581/10000000000 : ℝ)*x 0 + (2155738373/5000000000 : ℝ)*x 1 + (4311477091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503678581/10000000000 : ℝ)^2067 ≤ (8658463671867/25000000000000 : ℝ)^1555 := by
    have hnat : (4503678581 : ℕ)^2067*25000000000000^1555 ≤ 8658463671867^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503678581 10000000000 8658463671867 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155738373/5000000000 : ℝ)^2067 ≤ (6536614181687/20000000000000 : ℝ)^1555 := by
    have hnat : (2155738373 : ℕ)^2067*20000000000000^1555 ≤ 6536614181687^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155738373 5000000000 6536614181687 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4311477091/10000000000 : ℝ)^2067 ≤ (6536614876961/20000000000000 : ℝ)^1555 := by
    have hnat : (4311477091 : ℕ)^2067*20000000000000^1555 ≤ 6536614876961^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311477091 10000000000 6536614876961 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503678581/10000000000 : ℝ), (2155738373/5000000000 : ℝ), (4311477091/10000000000 : ℝ)] ![(8658463671867/25000000000000 : ℝ), (6536614181687/20000000000000 : ℝ), (6536614876961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503678581/10000000000 : ℝ)|^2067 ≤ (8658463671867/25000000000000 : ℝ)^1555
        have hw : |(4503678581/10000000000 : ℝ)|=(4503678581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2155738373/5000000000 : ℝ)|^2067 ≤ (6536614181687/20000000000000 : ℝ)^1555
        have hw : |(2155738373/5000000000 : ℝ)|=(2155738373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4311477091/10000000000 : ℝ)|^2067 ≤ (6536614876961/20000000000000 : ℝ)^1555
        have hw : |(4311477091/10000000000 : ℝ)|=(4311477091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_12 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062390791/5000000000 : ℝ)*x 0 + (680221299/1250000000 : ℝ)*x 1 + (5272216173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062390791/5000000000 : ℝ)^2067 ≤ (19936344081/156250000000 : ℝ)^1555 := by
    have hnat : (1062390791 : ℕ)^2067*156250000000^1555 ≤ 19936344081^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062390791 5000000000 19936344081 156250000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680221299/1250000000 : ℝ)^2067 ≤ (8907583717399/20000000000000 : ℝ)^1555 := by
    have hnat : (680221299 : ℕ)^2067*20000000000000^1555 ≤ 8907583717399^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680221299 1250000000 8907583717399 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272216173/10000000000 : ℝ)^2067 ≤ (42702821185721/100000000000000 : ℝ)^1555 := by
    have hnat : (5272216173 : ℕ)^2067*100000000000000^1555 ≤ 42702821185721^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272216173 10000000000 42702821185721 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062390791/5000000000 : ℝ), (680221299/1250000000 : ℝ), (5272216173/10000000000 : ℝ)] ![(19936344081/156250000000 : ℝ), (8907583717399/20000000000000 : ℝ), (42702821185721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062390791/5000000000 : ℝ)|^2067 ≤ (19936344081/156250000000 : ℝ)^1555
        have hw : |(-1062390791/5000000000 : ℝ)|=(1062390791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680221299/1250000000 : ℝ)|^2067 ≤ (8907583717399/20000000000000 : ℝ)^1555
        have hw : |(680221299/1250000000 : ℝ)|=(680221299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272216173/10000000000 : ℝ)|^2067 ≤ (42702821185721/100000000000000 : ℝ)^1555
        have hw : |(5272216173/10000000000 : ℝ)|=(5272216173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_13 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369616039/10000000000 : ℝ)*x 0 + (-277772603/1250000000 : ℝ)*x 1 + (5272216367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369616039/10000000000 : ℝ)^2067 ≤ (21877325244787/50000000000000 : ℝ)^1555 := by
    have hnat : (5369616039 : ℕ)^2067*50000000000000^1555 ≤ 21877325244787^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369616039 10000000000 21877325244787 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277772603/1250000000 : ℝ)^2067 ≤ (6771263113441/50000000000000 : ℝ)^1555 := by
    have hnat : (277772603 : ℕ)^2067*50000000000000^1555 ≤ 6771263113441^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277772603 1250000000 6771263113441 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272216367/10000000000 : ℝ)^2067 ≤ (2668926454651/6250000000000 : ℝ)^1555 := by
    have hnat : (5272216367 : ℕ)^2067*6250000000000^1555 ≤ 2668926454651^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272216367 10000000000 2668926454651 6250000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369616039/10000000000 : ℝ), (-277772603/1250000000 : ℝ), (5272216367/10000000000 : ℝ)] ![(21877325244787/50000000000000 : ℝ), (6771263113441/50000000000000 : ℝ), (2668926454651/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369616039/10000000000 : ℝ)|^2067 ≤ (21877325244787/50000000000000 : ℝ)^1555
        have hw : |(5369616039/10000000000 : ℝ)|=(5369616039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277772603/1250000000 : ℝ)|^2067 ≤ (6771263113441/50000000000000 : ℝ)^1555
        have hw : |(-277772603/1250000000 : ℝ)|=(277772603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272216367/10000000000 : ℝ)|^2067 ≤ (2668926454651/6250000000000 : ℝ)^1555
        have hw : |(5272216367/10000000000 : ℝ)|=(5272216367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_14 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369616109/10000000000 : ℝ)*x 0 + (1318054033/2500000000 : ℝ)*x 1 + (-1111090521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369616109/10000000000 : ℝ)^2067 ≤ (43754651247783/100000000000000 : ℝ)^1555 := by
    have hnat : (5369616109 : ℕ)^2067*100000000000000^1555 ≤ 43754651247783^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369616109 10000000000 43754651247783 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318054033/2500000000 : ℝ)^2067 ≤ (8540564148859/20000000000000 : ℝ)^1555 := by
    have hnat : (1318054033 : ℕ)^2067*20000000000000^1555 ≤ 8540564148859^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318054033 2500000000 8540564148859 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111090521/5000000000 : ℝ)^2067 ≤ (6771263996433/50000000000000 : ℝ)^1555 := by
    have hnat : (1111090521 : ℕ)^2067*50000000000000^1555 ≤ 6771263996433^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111090521 5000000000 6771263996433 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369616109/10000000000 : ℝ), (1318054033/2500000000 : ℝ), (-1111090521/5000000000 : ℝ)] ![(43754651247783/100000000000000 : ℝ), (8540564148859/20000000000000 : ℝ), (6771263996433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369616109/10000000000 : ℝ)|^2067 ≤ (43754651247783/100000000000000 : ℝ)^1555
        have hw : |(5369616109/10000000000 : ℝ)|=(5369616109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318054033/2500000000 : ℝ)|^2067 ≤ (8540564148859/20000000000000 : ℝ)^1555
        have hw : |(1318054033/2500000000 : ℝ)|=(1318054033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111090521/5000000000 : ℝ)|^2067 ≤ (6771263996433/50000000000000 : ℝ)^1555
        have hw : |(-1111090521/5000000000 : ℝ)|=(1111090521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_box_15 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061863709/2500000000 : ℝ)*x 0 + (887917179/2000000000 : ℝ)*x 1 + (4439586301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061863709/2500000000 : ℝ)^2067 ≤ (32039540644589/100000000000000 : ℝ)^1555 := by
    have hnat : (1061863709 : ℕ)^2067*100000000000000^1555 ≤ 32039540644589^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061863709 2500000000 32039540644589 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887917179/2000000000 : ℝ)^2067 ≤ (4247528450663/12500000000000 : ℝ)^1555 := by
    have hnat : (887917179 : ℕ)^2067*12500000000000^1555 ≤ 4247528450663^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887917179 2000000000 4247528450663 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4439586301/10000000000 : ℝ)^2067 ≤ (33980231735969/100000000000000 : ℝ)^1555 := by
    have hnat : (4439586301 : ℕ)^2067*100000000000000^1555 ≤ 33980231735969^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439586301 10000000000 33980231735969 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061863709/2500000000 : ℝ), (887917179/2000000000 : ℝ), (4439586301/10000000000 : ℝ)] ![(32039540644589/100000000000000 : ℝ), (4247528450663/12500000000000 : ℝ), (33980231735969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061863709/2500000000 : ℝ)|^2067 ≤ (32039540644589/100000000000000 : ℝ)^1555
        have hw : |(1061863709/2500000000 : ℝ)|=(1061863709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(887917179/2000000000 : ℝ)|^2067 ≤ (4247528450663/12500000000000 : ℝ)^1555
        have hw : |(887917179/2000000000 : ℝ)|=(887917179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4439586301/10000000000 : ℝ)|^2067 ≤ (33980231735969/100000000000000 : ℝ)^1555
        have hw : |(4439586301/10000000000 : ℝ)|=(4439586301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1075_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59247/100000 : ℝ) ∧ (79601/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82973/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1751/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1751/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1751/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1751/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1751/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1751/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (352/3125 : ℝ) ^ (8267/2048 : ℝ) ≤ (1857601390703937/12500000000000000000 : ℝ) := by
    have hpowers : (352/3125 : ℝ)^8267 ≤ (1857601390703937/12500000000000000000 : ℝ)^2048 := by
      have hnat : (352 : ℕ)^8267*12500000000000000000^2048 ≤ 1857601390703937^2048*3125^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        352 3125 1857601390703937 12500000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (352/3125 : ℝ)) (X := (1857601390703937/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1751/12500 : ℝ) ^ (8267/2048 : ℝ) ≤ (17494999739/48828125000000 : ℝ) := by
    have hpowers : (1751/12500 : ℝ)^8267 ≤ (17494999739/48828125000000 : ℝ)^2048 := by
      have hnat : (1751 : ℕ)^8267*48828125000000^2048 ≤ 17494999739^2048*12500^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1751 12500 17494999739 48828125000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1751/12500 : ℝ)) (X := (17494999739/48828125000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251857601390703937/6250000000000000000 : ℝ) ≤ (5000368108616891/5000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (6251857601390703937/6250000000000000000 : ℝ)^2048 ≤ (5000368108616891/5000000000000000 : ℝ)^8267 := by
      have hnat : (6251857601390703937 : ℕ)^2048*5000000000000000^8267 ≤ 5000368108616891^8267*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251857601390703937 6250000000000000000 5000368108616891 5000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000368108616891/5000000000000000 : ℝ)) (X := (6251857601390703937/6250000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506336321323887937/12500000000000000000 : ℝ) ≤ (10001255528011749/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (12506336321323887937/12500000000000000000 : ℝ)^2048 ≤ (10001255528011749/10000000000000000 : ℝ)^8267 := by
      have hnat : (12506336321323887937 : ℕ)^2048*10000000000000000^8267 ≤ 10001255528011749^8267*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506336321323887937 12500000000000000000 10001255528011749 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001255528011749/10000000000000000 : ℝ)) (X := (12506336321323887937/12500000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (24431557499739/24414062500000 : ℝ) ≤ (2500443709697429/2500000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (24431557499739/24414062500000 : ℝ)^2048 ≤ (2500443709697429/2500000000000000 : ℝ)^8267 := by
      have hnat : (24431557499739 : ℕ)^2048*2500000000000000^8267 ≤ 2500443709697429^8267*24414062500000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24431557499739 24414062500000 2500443709697429 2500000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500443709697429/2500000000000000 : ℝ)) (X := (24431557499739/24414062500000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1857601390703937/12500000000000000000 : ℝ) ≤ ((1714395071680216077/1715000000000000000 : ℝ)+2*(519310777967/274400000000000 : ℝ)*(352/3125 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (1714395071680216077/1715000000000000000 : ℝ)+2*(519310777967/274400000000000 : ℝ)*(352/3125 : ℝ)=(5000368108616891/5000000000000000 : ℝ) by norm_num, show 1+2*(1857601390703937/12500000000000000000 : ℝ)=(6251857601390703937/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17494999739/48828125000000 : ℝ)+(1857601390703937/12500000000000000000 : ℝ) ≤ ((1714395071680216077/1715000000000000000 : ℝ)+(519310777967/274400000000000 : ℝ)*((1751/12500 : ℝ)+(352/3125 : ℝ)))^(8267/2048 : ℝ) := by
    rw [show (1714395071680216077/1715000000000000000 : ℝ)+(519310777967/274400000000000 : ℝ)*((1751/12500 : ℝ)+(352/3125 : ℝ))=(10001255528011749/10000000000000000 : ℝ) by norm_num, show 1+(17494999739/48828125000000 : ℝ)+(1857601390703937/12500000000000000000 : ℝ)=(12506336321323887937/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17494999739/48828125000000 : ℝ) ≤ ((1714395071680216077/1715000000000000000 : ℝ)+2*(519310777967/274400000000000 : ℝ)*(1751/12500 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (1714395071680216077/1715000000000000000 : ℝ)+2*(519310777967/274400000000000 : ℝ)*(1751/12500 : ℝ)=(2500443709697429/2500000000000000 : ℝ) by norm_num, show 1+2*(17494999739/48828125000000 : ℝ)=(24431557499739/24414062500000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1714395071680216077/1715000000000000000 : ℝ)*(X 1 0+X 2 0)+(519310777967/274400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (1714395071680216077/1715000000000000000 : ℝ)) (alpha := (519310777967/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1714395071680216077/1715000000000000000 : ℝ)*(X 0 1+X 2 1)+(519310777967/274400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (1714395071680216077/1715000000000000000 : ℝ)) (alpha := (519310777967/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1714395071680216077/1715000000000000000 : ℝ)*(X 0 2+X 1 2)+(519310777967/274400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (1714395071680216077/1715000000000000000 : ℝ)) (alpha := (519310777967/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-41403891/200000000 : ℝ)*X 0 0+(268862261/500000000 : ℝ)*X 0 1+(672155629/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647651383/5000000000 : ℝ)*X 1 0+(-545286831/2500000000 : ℝ)*X 1 1+(2688622517/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647651441/5000000000 : ℝ)*X 2 0+(1344311237/2500000000 : ℝ)*X 2 1+(-545286821/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4482485641/10000000000 : ℝ)*X 0 0+(4322213853/10000000000 : ℝ)*X 0 1+(2161106993/5000000000 : ℝ)*X 0 2+(4482485641/10000000000 : ℝ)*X 1 0+(4322213853/10000000000 : ℝ)*X 1 1+(2161106993/5000000000 : ℝ)*X 1 2+(4482485641/10000000000 : ℝ)*X 2 0+(4322213853/10000000000 : ℝ)*X 2 1+(2161106993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1164943149/5000000000 : ℝ)*X 0 0+(5280222467/10000000000 : ℝ)*X 0 1+(2640111033/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072790681/2000000000 : ℝ)*X 1 0+(-44382153/200000000 : ℝ)*X 1 1+(5280222017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((670494123/1250000000 : ℝ)*X 2 0+(5280222543/10000000000 : ℝ)*X 2 1+(-2219107513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2132791139/5000000000 : ℝ)*X 0 0+(708903/1600000 : ℝ)*X 0 1+(4430644677/10000000000 : ℝ)*X 0 2+(2132791139/5000000000 : ℝ)*X 1 0+(708903/1600000 : ℝ)*X 1 1+(4430644677/10000000000 : ℝ)*X 1 2+(2132791139/5000000000 : ℝ)*X 2 0+(708903/1600000 : ℝ)*X 2 1+(4430644677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2275662099/10000000000 : ℝ)*X 0 0+(1303592129/2500000000 : ℝ)*X 0 1+(2693423581/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288504917/10000000000 : ℝ)*X 1 0+(-2177320153/10000000000 : ℝ)*X 1 1+(2693423499/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((264425249/500000000 : ℝ)*X 2 0+(5386847129/10000000000 : ℝ)*X 2 1+(-544329973/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4503678581/10000000000 : ℝ)*X 0 0+(2155738373/5000000000 : ℝ)*X 0 1+(4311477091/10000000000 : ℝ)*X 0 2+(4503678581/10000000000 : ℝ)*X 1 0+(2155738373/5000000000 : ℝ)*X 1 1+(4311477091/10000000000 : ℝ)*X 1 2+(4503678581/10000000000 : ℝ)*X 2 0+(2155738373/5000000000 : ℝ)*X 2 1+(4311477091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1062390791/5000000000 : ℝ)*X 0 0+(680221299/1250000000 : ℝ)*X 0 1+(5272216173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369616039/10000000000 : ℝ)*X 1 0+(-277772603/1250000000 : ℝ)*X 1 1+(5272216367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369616109/10000000000 : ℝ)*X 2 0+(1318054033/2500000000 : ℝ)*X 2 1+(-1111090521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1061863709/2500000000 : ℝ)*X 0 0+(887917179/2000000000 : ℝ)*X 0 1+(4439586301/10000000000 : ℝ)*X 0 2+(1061863709/2500000000 : ℝ)*X 1 0+(887917179/2000000000 : ℝ)*X 1 1+(4439586301/10000000000 : ℝ)*X 1 2+(1061863709/2500000000 : ℝ)*X 2 0+(887917179/2000000000 : ℝ)*X 2 1+(4439586301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-53355888576959947562014447965063/85750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (315087571/100000000000000 : ℝ)*(upper0) + (24945061/20000000000000 : ℝ)*(upper1) + (31992199/50000000000000 : ℝ)*(upper2) + (99533861/100000000000000 : ℝ)*(upper3) + (69309819/50000000000000 : ℝ)*(upper5) + (241510890410093/6250000000000 : ℝ)*(major0) + (241510890410093/6250000000000 : ℝ)*(major1) + (3864174246561489/100000000000000 : ℝ)*(major2) + (253195533/1562500000000 : ℝ)*(sp3) + (205644954897343/4000000000000 : ℝ)*(sp4) + (205644954897343/4000000000000 : ℝ)*(sp5) + (5140854662559467/100000000000000 : ℝ)*(sp6) + (162996830398143/6250000000000 : ℝ)*(sp7) + (67302468527/25000000000000 : ℝ)*(sp14) + (6519913727211/250000000000 : ℝ)*(f.failure) + (205644954897343/4000000000000 : ℝ)*(f.sum) + (35687360123119/27440000000000000000000000000 : ℝ)*base65 + (1111052773199731837/85750000000000000000000000000000 : ℝ)*base68 + (118694447973017041347/171500000000000000000000000000000 : ℝ)*base70 + (871893593902231837/85750000000000000000000000000000 : ℝ)*base72 + (95508171880081/27440000000000000000000000000 : ℝ)*base74 + (10692452425504541347/171500000000000000000000000000000 : ℝ)*base76 + (87894961940891089/10718750000000000000000000000000 : ℝ)*base78 + (1501548374389390161/10718750000000000000000000000000 : ℝ)*base79 + (570291162939353/1715000000000000000000000000 : ℝ)*base82 + (256861/25000000000000000000 : ℝ)*base89 + (256861/25000000000000000000 : ℝ)*base91 + (6861/25000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59247/100000 : ℝ) ≤ (453632644164953826293048429949/765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63551/156250000000 : ℝ)*(upper0) + (2505903/12500000000000 : ℝ)*(lower1) + (51733891/100000000000000 : ℝ)*(upper4) + (490902150950203/12500000000000 : ℝ)*(major0) + (490902150950203/12500000000000 : ℝ)*(major1) + (490902150950203/12500000000000 : ℝ)*(major2) + (2592083325384891/50000000000000 : ℝ)*(sp0) + (2592073426130917/50000000000000 : ℝ)*(sp1) + (2592067246015769/50000000000000 : ℝ)*(sp2) + (662627548213523/25000000000000 : ℝ)*(sp3) + (2013504581/50000000000000 : ℝ)*(sp8) + (23825517109/100000000000000 : ℝ)*(sp9) + (7237149481/20000000000000 : ℝ)*(sp10) + (3551899073/100000000000000 : ℝ)*(sp11) + (530102748950633/20000000000000 : ℝ)*(f.failure) + (5184170677778943/100000000000000 : ℝ)*(f.sum) + (289059347663/214375000000000000000000000 : ℝ)*base66 + (239102421243480119/21437500000000000000000000000000 : ℝ)*base68 + (322464499340417619/21437500000000000000000000000000 : ℝ)*base70 + (134256488261480119/21437500000000000000000000000000 : ℝ)*base72 + (17387386519007/857500000000000000000000000 : ℝ)*base74 + (66406421553542619/21437500000000000000000000000000 : ℝ)*base76 + (45383081406207381/21437500000000000000000000000000 : ℝ)*base77 + (1219960970024167619/21437500000000000000000000000000 : ℝ)*base80 + (93278175293/214375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1889583/2000000000000000000000 : ℝ)*base89 + (1889583/2000000000000000000000 : ℝ)*base91 + (1889583/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79601/100000 : ℝ) ≤ (6825957510361890675279617672253/8575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51225911/50000000000000 : ℝ)*(upper0) + (109822547/100000000000000 : ℝ)*(lower3) + (110043051/100000000000000 : ℝ)*(upper4) + (439543999412237/10000000000000 : ℝ)*(major0) + (439543999412237/10000000000000 : ℝ)*(major1) + (439543999412237/10000000000000 : ℝ)*(major2) + (121155757/250000000000 : ℝ)*(sp1) + (39152043127/25000000000000 : ℝ)*(sp2) + (1618430237/3125000000000 : ℝ)*(sp3) + (745488141/25000000000000 : ℝ)*(sp4) + (45295478229817/781250000000 : ℝ)*(sp8) + (5797775733066339/100000000000000 : ℝ)*(sp9) + (5797667587196631/100000000000000 : ℝ)*(sp10) + (185404354297661/6250000000000 : ℝ)*(sp11) + (37081518231627/1250000000000 : ℝ)*(f.failure) + (5797824195369139/100000000000000 : ℝ)*(f.sum) + (7392923213891/1372000000000000000000000000 : ℝ)*base65 + (80361058705247001/17150000000000000000000000000000 : ℝ)*base68 + (136613664511847001/17150000000000000000000000000000 : ℝ)*base70 + (209636794076102999/17150000000000000000000000000000 : ℝ)*base71 + (2052112581353/1372000000000000000000000000 : ℝ)*base74 + (66890619578252999/17150000000000000000000000000000 : ℝ)*base75 + (93187320419152999/17150000000000000000000000000000 : ℝ)*base77 + (805121989544902999/17150000000000000000000000000000 : ℝ)*base79 + (4838867304973/1372000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (188323/125000000000000000000 : ℝ)*base90 + (188323/125000000000000000000 : ℝ)*base92 + (188323/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-82973/100000 : ℝ) ≤ (-1111675685473287118436307265647/1339843750000000000000000000000 : ℝ) := by norm_num
    linear_combination (962257/5000000000000 : ℝ)*(lower0) + (44666719/50000000000000 : ℝ)*(lower1) + (101089741/100000000000000 : ℝ)*(lower4) + (276876318188173/6250000000000 : ℝ)*(major0) + (276876318188173/6250000000000 : ℝ)*(major1) + (276876318188173/6250000000000 : ℝ)*(major2) + (1526100743/12500000000000 : ℝ)*(sp0) + (64418920641/50000000000000 : ℝ)*(sp5) + (1901165567/500000000000 : ℝ)*(sp6) + (11517178733/50000000000000 : ℝ)*(sp7) + (1474456568610309/25000000000000 : ℝ)*(sp12) + (2948854822702949/50000000000000 : ℝ)*(sp13) + (5897458250133781/100000000000000 : ℝ)*(sp14) + (2989837513346047/100000000000000 : ℝ)*(sp15) + (373732568462939/12500000000000 : ℝ)*(f.failure) + (294891924162359/5000000000000 : ℝ)*(f.sum) + (5580174612669/857500000000000000000000000 : ℝ)*base66 + (90775549823582321/10718750000000000000000000000000 : ℝ)*base67 + (4014364252792679/10718750000000000000000000000000 : ℝ)*base70 + (5828977959073929/10718750000000000000000000000000 : ℝ)*base72 + (21729685776787/1715000000000000000000000000 : ℝ)*base73 + (84324660586832321/10718750000000000000000000000000 : ℝ)*base75 + (563679213707321/10718750000000000000000000000000 : ℝ)*base77 + (172115222595457321/10718750000000000000000000000000 : ℝ)*base79 + (7239617653277/1715000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16344211/1250000000000000000000 : ℝ)*base90 + (16344211/1250000000000000000000 : ℝ)*base92 + (16344211/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1075_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59247/100000 : ℝ) else (79601/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82973/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1075_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1075_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59247/100000 : ℝ) else (79601/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82973/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1075_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1075_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59247/100000 : ℝ) else (79601/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82973/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1075_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
