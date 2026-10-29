-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1549_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:28.726992+00:00
-- url     : https://prove2.me/submissions/ae4748eb-5096-4736-9bd3-4eebf74b882c

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
theorem support_rectangle_w1549_s0_0 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-25738831/156250000 : ℝ)*x 0 + (1176980689/2000000000 : ℝ)*x 1 + (2435413871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25738831/156250000 : ℝ)^4595 ≤ (1227676102371/12500000000000 : ℝ)^3571 := by
    have hnat : (25738831 : ℕ)^4595*12500000000000^3571 ≤ 1227676102371^3571*156250000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25738831 156250000 1227676102371 12500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1176980689/2000000000 : ℝ)^4595 ≤ (50548827023389/100000000000000 : ℝ)^3571 := by
    have hnat : (1176980689 : ℕ)^4595*100000000000000^3571 ≤ 50548827023389^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176980689 2000000000 50548827023389 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2435413871/5000000000 : ℝ)^4595 ≤ (19814882071651/50000000000000 : ℝ)^3571 := by
    have hnat : (2435413871 : ℕ)^4595*50000000000000^3571 ≤ 19814882071651^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435413871 5000000000 19814882071651 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25738831/156250000 : ℝ), (1176980689/2000000000 : ℝ), (2435413871/5000000000 : ℝ)] ![(1227676102371/12500000000000 : ℝ), (50548827023389/100000000000000 : ℝ), (19814882071651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25738831/156250000 : ℝ)|^4595 ≤ (1227676102371/12500000000000 : ℝ)^3571
        have hw : |(-25738831/156250000 : ℝ)|=(25738831/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1176980689/2000000000 : ℝ)|^4595 ≤ (50548827023389/100000000000000 : ℝ)^3571
        have hw : |(1176980689/2000000000 : ℝ)|=(1176980689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2435413871/5000000000 : ℝ)|^4595 ≤ (19814882071651/50000000000000 : ℝ)^3571
        have hw : |(2435413871/5000000000 : ℝ)|=(2435413871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s0_1 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1367493953/2500000000 : ℝ)*x 0 + (-2213046603/10000000000 : ℝ)*x 1 + (4870827739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1367493953/2500000000 : ℝ)^4595 ≤ (46009929247969/100000000000000 : ℝ)^3571 := by
    have hnat : (1367493953 : ℕ)^4595*100000000000000^3571 ≤ 46009929247969^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367493953 2500000000 46009929247969 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213046603/10000000000 : ℝ)^4595 ≤ (7180153318441/50000000000000 : ℝ)^3571 := by
    have hnat : (2213046603 : ℕ)^4595*50000000000000^3571 ≤ 7180153318441^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213046603 10000000000 7180153318441 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4870827739/10000000000 : ℝ)^4595 ≤ (19814882055947/50000000000000 : ℝ)^3571 := by
    have hnat : (4870827739 : ℕ)^4595*50000000000000^3571 ≤ 19814882055947^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870827739 10000000000 19814882055947 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1367493953/2500000000 : ℝ), (-2213046603/10000000000 : ℝ), (4870827739/10000000000 : ℝ)] ![(46009929247969/100000000000000 : ℝ), (7180153318441/50000000000000 : ℝ), (19814882055947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1367493953/2500000000 : ℝ)|^4595 ≤ (46009929247969/100000000000000 : ℝ)^3571
        have hw : |(1367493953/2500000000 : ℝ)|=(1367493953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213046603/10000000000 : ℝ)|^4595 ≤ (7180153318441/50000000000000 : ℝ)^3571
        have hw : |(-2213046603/10000000000 : ℝ)|=(2213046603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4870827739/10000000000 : ℝ)|^4595 ≤ (19814882055947/50000000000000 : ℝ)^3571
        have hw : |(4870827739/10000000000 : ℝ)|=(4870827739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s0_2 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093995169/2000000000 : ℝ)*x 0 + (48708277/100000000 : ℝ)*x 1 + (-138315413/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093995169/2000000000 : ℝ)^4595 ≤ (46009929605139/100000000000000 : ℝ)^3571 := by
    have hnat : (1093995169 : ℕ)^4595*100000000000000^3571 ≤ 46009929605139^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093995169 2000000000 46009929605139 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48708277/100000000 : ℝ)^4595 ≤ (7925952740719/20000000000000 : ℝ)^3571 := by
    have hnat : (48708277 : ℕ)^4595*20000000000000^3571 ≤ 7925952740719^3571*100000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48708277 100000000 7925952740719 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138315413/625000000 : ℝ)^4595 ≤ (14360306678631/100000000000000 : ℝ)^3571 := by
    have hnat : (138315413 : ℕ)^4595*100000000000000^3571 ≤ 14360306678631^3571*625000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138315413 625000000 14360306678631 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093995169/2000000000 : ℝ), (48708277/100000000 : ℝ), (-138315413/625000000 : ℝ)] ![(46009929605139/100000000000000 : ℝ), (7925952740719/20000000000000 : ℝ), (14360306678631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093995169/2000000000 : ℝ)|^4595 ≤ (46009929605139/100000000000000 : ℝ)^3571
        have hw : |(1093995169/2000000000 : ℝ)|=(1093995169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48708277/100000000 : ℝ)|^4595 ≤ (7925952740719/20000000000000 : ℝ)^3571
        have hw : |(48708277/100000000 : ℝ)|=(48708277/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138315413/625000000 : ℝ)|^4595 ≤ (14360306678631/100000000000000 : ℝ)^3571
        have hw : |(-138315413/625000000 : ℝ)|=(138315413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s0_3 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135310719/10000000000 : ℝ)*x 0 + (618431943/2000000000 : ℝ)*x 1 + (2725870591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135310719/10000000000 : ℝ)^4595 ≤ (1605129850109/5000000000000 : ℝ)^3571 := by
    have hnat : (4135310719 : ℕ)^4595*5000000000000^3571 ≤ 1605129850109^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135310719 10000000000 1605129850109 5000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618431943/2000000000 : ℝ)^4595 ≤ (4416947835311/20000000000000 : ℝ)^3571 := by
    have hnat : (618431943 : ℕ)^4595*20000000000000^3571 ≤ 4416947835311^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618431943 2000000000 4416947835311 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725870591/5000000000 : ℝ)^4595 ≤ (5726582976843/12500000000000 : ℝ)^3571 := by
    have hnat : (2725870591 : ℕ)^4595*12500000000000^3571 ≤ 5726582976843^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725870591 5000000000 5726582976843 12500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135310719/10000000000 : ℝ), (618431943/2000000000 : ℝ), (2725870591/5000000000 : ℝ)] ![(1605129850109/5000000000000 : ℝ), (4416947835311/20000000000000 : ℝ), (5726582976843/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135310719/10000000000 : ℝ)|^4595 ≤ (1605129850109/5000000000000 : ℝ)^3571
        have hw : |(4135310719/10000000000 : ℝ)|=(4135310719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618431943/2000000000 : ℝ)|^4595 ≤ (4416947835311/20000000000000 : ℝ)^3571
        have hw : |(618431943/2000000000 : ℝ)|=(618431943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725870591/5000000000 : ℝ)|^4595 ≤ (5726582976843/12500000000000 : ℝ)^3571
        have hw : |(2725870591/5000000000 : ℝ)|=(2725870591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s0_4 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-412625593/2500000000 : ℝ)*x 0 + (4896501441/10000000000 : ℝ)*x 1 + (1464578923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412625593/2500000000 : ℝ)^4595 ≤ (9846097542689/100000000000000 : ℝ)^3571 := by
    have hnat : (412625593 : ℕ)^4595*100000000000000^3571 ≤ 9846097542689^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412625593 2500000000 9846097542689 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4896501441/10000000000 : ℝ)^4595 ≤ (7979750130907/20000000000000 : ℝ)^3571 := by
    have hnat : (4896501441 : ℕ)^4595*20000000000000^3571 ≤ 7979750130907^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4896501441 10000000000 7979750130907 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1464578923/2500000000 : ℝ)^4595 ≤ (50255151789279/100000000000000 : ℝ)^3571 := by
    have hnat : (1464578923 : ℕ)^4595*100000000000000^3571 ≤ 50255151789279^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464578923 2500000000 50255151789279 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412625593/2500000000 : ℝ), (4896501441/10000000000 : ℝ), (1464578923/2500000000 : ℝ)] ![(9846097542689/100000000000000 : ℝ), (7979750130907/20000000000000 : ℝ), (50255151789279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412625593/2500000000 : ℝ)|^4595 ≤ (9846097542689/100000000000000 : ℝ)^3571
        have hw : |(-412625593/2500000000 : ℝ)|=(412625593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4896501441/10000000000 : ℝ)|^4595 ≤ (7979750130907/20000000000000 : ℝ)^3571
        have hw : |(4896501441/10000000000 : ℝ)|=(4896501441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1464578923/2500000000 : ℝ)|^4595 ≤ (50255151789279/100000000000000 : ℝ)^3571
        have hw : |(1464578923/2500000000 : ℝ)|=(1464578923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s0_5 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038558729/2000000000 : ℝ)*x 0 + (-1225559111/10000000000 : ℝ)*x 1 + (5858315307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038558729/2000000000 : ℝ)^4595 ≤ (2151597688379/5000000000000 : ℝ)^3571 := by
    have hnat : (1038558729 : ℕ)^4595*5000000000000^3571 ≤ 2151597688379^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038558729 2000000000 2151597688379 5000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1225559111/10000000000 : ℝ)^4595 ≤ (1678224668481/25000000000000 : ℝ)^3571 := by
    have hnat : (1225559111 : ℕ)^4595*25000000000000^3571 ≤ 1678224668481^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225559111 10000000000 1678224668481 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5858315307/10000000000 : ℝ)^4595 ≤ (50255147539521/100000000000000 : ℝ)^3571 := by
    have hnat : (5858315307 : ℕ)^4595*100000000000000^3571 ≤ 50255147539521^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5858315307 10000000000 50255147539521 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038558729/2000000000 : ℝ), (-1225559111/10000000000 : ℝ), (5858315307/10000000000 : ℝ)] ![(2151597688379/5000000000000 : ℝ), (1678224668481/25000000000000 : ℝ), (50255147539521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038558729/2000000000 : ℝ)|^4595 ≤ (2151597688379/5000000000000 : ℝ)^3571
        have hw : |(1038558729/2000000000 : ℝ)|=(1038558729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1225559111/10000000000 : ℝ)|^4595 ≤ (1678224668481/25000000000000 : ℝ)^3571
        have hw : |(-1225559111/10000000000 : ℝ)|=(1225559111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5858315307/10000000000 : ℝ)|^4595 ≤ (50255147539521/100000000000000 : ℝ)^3571
        have hw : |(5858315307/10000000000 : ℝ)|=(5858315307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s0_6 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41542343/80000000 : ℝ)*x 0 + (1464579133/2500000000 : ℝ)*x 1 + (-1225558359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41542343/80000000 : ℝ)^4595 ≤ (43031945556951/100000000000000 : ℝ)^3571 := by
    have hnat : (41542343 : ℕ)^4595*100000000000000^3571 ≤ 43031945556951^3571*80000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41542343 80000000 43031945556951 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1464579133/2500000000 : ℝ)^4595 ≤ (25127580530739/50000000000000 : ℝ)^3571 := by
    have hnat : (1464579133 : ℕ)^4595*50000000000000^3571 ≤ 25127580530739^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464579133 2500000000 25127580530739 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1225558359/10000000000 : ℝ)^4595 ≤ (20977791793/312500000000 : ℝ)^3571 := by
    have hnat : (1225558359 : ℕ)^4595*312500000000^3571 ≤ 20977791793^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225558359 10000000000 20977791793 312500000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41542343/80000000 : ℝ), (1464579133/2500000000 : ℝ), (-1225558359/10000000000 : ℝ)] ![(43031945556951/100000000000000 : ℝ), (25127580530739/50000000000000 : ℝ), (20977791793/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41542343/80000000 : ℝ)|^4595 ≤ (43031945556951/100000000000000 : ℝ)^3571
        have hw : |(41542343/80000000 : ℝ)|=(41542343/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1464579133/2500000000 : ℝ)|^4595 ≤ (25127580530739/50000000000000 : ℝ)^3571
        have hw : |(1464579133/2500000000 : ℝ)|=(1464579133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1225558359/10000000000 : ℝ)|^4595 ≤ (20977791793/312500000000 : ℝ)^3571
        have hw : |(-1225558359/10000000000 : ℝ)|=(1225558359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s0_7 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4142794503/10000000000 : ℝ)*x 0 + (5392001561/10000000000 : ℝ)*x 1 + (315402411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142794503/10000000000 : ℝ)^4595 ≤ (201108580537/625000000000 : ℝ)^3571 := by
    have hnat : (4142794503 : ℕ)^4595*625000000000^3571 ≤ 201108580537^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142794503 10000000000 201108580537 625000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392001561/10000000000 : ℝ)^4595 ≤ (2822982322663/6250000000000 : ℝ)^3571 := by
    have hnat : (5392001561 : ℕ)^4595*6250000000000^3571 ≤ 2822982322663^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392001561 10000000000 2822982322663 6250000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315402411/1000000000 : ℝ)^4595 ≤ (1415931870553/6250000000000 : ℝ)^3571 := by
    have hnat : (315402411 : ℕ)^4595*6250000000000^3571 ≤ 1415931870553^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315402411 1000000000 1415931870553 6250000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142794503/10000000000 : ℝ), (5392001561/10000000000 : ℝ), (315402411/1000000000 : ℝ)] ![(201108580537/625000000000 : ℝ), (2822982322663/6250000000000 : ℝ), (1415931870553/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142794503/10000000000 : ℝ)|^4595 ≤ (201108580537/625000000000 : ℝ)^3571
        have hw : |(4142794503/10000000000 : ℝ)|=(4142794503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392001561/10000000000 : ℝ)|^4595 ≤ (2822982322663/6250000000000 : ℝ)^3571
        have hw : |(5392001561/10000000000 : ℝ)|=(5392001561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315402411/1000000000 : ℝ)|^4595 ≤ (1415931870553/6250000000000 : ℝ)^3571
        have hw : |(315402411/1000000000 : ℝ)|=(315402411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1549_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (823/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12507/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4593/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4593 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4593*1^1024 ≤ 0^1024*1^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4593/1024 : ℝ) ≤ (410241100938803053/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4593 ≤ (410241100938803053/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4593*25000000000000000000^1024 ≤ 410241100938803053^1024*5^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 410241100938803053 25000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (410241100938803053/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4593 := by
      have hnat : (1 : ℕ)^1024*1^4593 ≤ 1^4593*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25410241100938803053/25000000000000000000 : ℝ) ≤ (1003635395891491/1000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (25410241100938803053/25000000000000000000 : ℝ)^1024 ≤ (1003635395891491/1000000000000000 : ℝ)^4593 := by
      have hnat : (25410241100938803053 : ℕ)^1024*1000000000000000^4593 ≤ 1003635395891491^4593*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25410241100938803053 25000000000000000000 1003635395891491 1000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1003635395891491/1000000000000000 : ℝ)) (X := (25410241100938803053/25000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12910241100938803053/12500000000000000000 : ℝ) ≤ (503635395891491/500000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (12910241100938803053/12500000000000000000 : ℝ)^1024 ≤ (503635395891491/500000000000000 : ℝ)^4593 := by
      have hnat : (12910241100938803053 : ℕ)^1024*500000000000000^4593 ≤ 503635395891491^4593*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12910241100938803053 12500000000000000000 503635395891491 500000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (503635395891491/500000000000000 : ℝ)) (X := (12910241100938803053/12500000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3635395891491/400000000000000 : ℝ)*(0 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3635395891491/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(410241100938803053/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3635395891491/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4593/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3635395891491/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1003635395891491/1000000000000000 : ℝ) by norm_num, show 1+(410241100938803053/25000000000000000000 : ℝ)+(0 : ℝ)=(25410241100938803053/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(410241100938803053/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3635395891491/400000000000000 : ℝ)*(2/5 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3635395891491/400000000000000 : ℝ)*(2/5 : ℝ)=(503635395891491/500000000000000 : ℝ) by norm_num, show 1+2*(410241100938803053/25000000000000000000 : ℝ)=(12910241100938803053/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3635395891491/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3635395891491/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3635395891491/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3635395891491/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3635395891491/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3635395891491/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-25738831/156250000 : ℝ)*X 0 0+(1176980689/2000000000 : ℝ)*X 0 1+(2435413871/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1367493953/2500000000 : ℝ)*X 1 0+(-2213046603/10000000000 : ℝ)*X 1 1+(4870827739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1093995169/2000000000 : ℝ)*X 2 0+(48708277/100000000 : ℝ)*X 2 1+(-138315413/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4135310719/10000000000 : ℝ)*X 0 0+(618431943/2000000000 : ℝ)*X 0 1+(2725870591/5000000000 : ℝ)*X 0 2+(4135310719/10000000000 : ℝ)*X 1 0+(618431943/2000000000 : ℝ)*X 1 1+(2725870591/5000000000 : ℝ)*X 1 2+(4135310719/10000000000 : ℝ)*X 2 0+(618431943/2000000000 : ℝ)*X 2 1+(2725870591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-412625593/2500000000 : ℝ)*X 0 0+(4896501441/10000000000 : ℝ)*X 0 1+(1464578923/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1038558729/2000000000 : ℝ)*X 1 0+(-1225559111/10000000000 : ℝ)*X 1 1+(5858315307/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41542343/80000000 : ℝ)*X 2 0+(1464579133/2500000000 : ℝ)*X 2 1+(-1225558359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4142794503/10000000000 : ℝ)*X 0 0+(5392001561/10000000000 : ℝ)*X 0 1+(315402411/1000000000 : ℝ)*X 0 2+(4142794503/10000000000 : ℝ)*X 1 0+(5392001561/10000000000 : ℝ)*X 1 1+(315402411/1000000000 : ℝ)*X 1 2+(4142794503/10000000000 : ℝ)*X 2 0+(5392001561/10000000000 : ℝ)*X 2 1+(315402411/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (610362224096399937/244140625000000000000000 : ℝ) := by norm_num
    linear_combination (25067853/100000000000000 : ℝ)*(base1) + (517809011/100000000000000 : ℝ)*(base19) + (20950329/4000000000000 : ℝ)*(base23) + (66311349/100000000000000 : ℝ)*(upper3) + (66359853/100000000000000 : ℝ)*(upper5) + (1376883772283/195312500000 : ℝ)*(major0) + (1376883772283/195312500000 : ℝ)*(major1) + (1376883772283/195312500000 : ℝ)*(major2) + (986121458004623/100000000000000 : ℝ)*(sp0) + (246530701637979/25000000000000 : ℝ)*(sp1) + (986122800602703/100000000000000 : ℝ)*(sp2) + (10595118472823/2500000000000 : ℝ)*(sp3) + (945712079/50000000000000 : ℝ)*(sp4) + (811141297/100000000000000 : ℝ)*(sp7) + (423805575122069/100000000000000 : ℝ)*(f.failure) + (30816353886279/3125000000000 : ℝ)*(f.sum) + (499215661127/625000000000000000000000000 : ℝ)*base66 + (2521345977313/312500000000000000000000000 : ℝ)*base68 + (62210620209/9765625000000000000000000 : ℝ)*base70 + (1826014037751/625000000000000000000000000 : ℝ)*base72 + (1713384164877/625000000000000000000000000 : ℝ)*base74 + (295366615187/312500000000000000000000000 : ℝ)*base75 + (1290961157313/312500000000000000000000000 : ℝ)*base78 + (4142338946501/625000000000000000000000000 : ℝ)*base80 + (580166962751/312500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5572733/5000000000000000000000 : ℝ)*base90 + (5572733/5000000000000000000000 : ℝ)*base92 + (5572733/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26328237691569095229717/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1564036533/100000000000000 : ℝ)*(base19) + (1719636777/100000000000000 : ℝ)*(base23) + (158584621/50000000000000 : ℝ)*(base39) + (18514539/10000000000000 : ℝ)*(upper3) + (389795429/100000000000000 : ℝ)*(upper5) + (148653189978029/20000000000000 : ℝ)*(major0) + (148653189978029/20000000000000 : ℝ)*(major1) + (743265632720903/100000000000000 : ℝ)*(major2) + (2139777711/50000000000000 : ℝ)*(sp1) + (169796259/4000000000000 : ℝ)*(sp2) + (519849993863789/50000000000000 : ℝ)*(sp4) + (519847072067811/50000000000000 : ℝ)*(sp5) + (1039694340353567/100000000000000 : ℝ)*(sp6) + (446831375481487/100000000000000 : ℝ)*(sp7) + (446831375481487/100000000000000 : ℝ)*(f.failure) + (1039700304896819/100000000000000 : ℝ)*(f.sum) + (2529428499071/5000000000000000000000000000 : ℝ)*base65 + (91579968663627/40000000000000000000000000000 : ℝ)*base68 + (78078486316761/8000000000000000000000000000 : ℝ)*base70 + (40740042936373/40000000000000000000000000000 : ℝ)*base71 + (9062905270929/5000000000000000000000000000 : ℝ)*base74 + (6826189004761/8000000000000000000000000000 : ℝ)*base76 + (9287978363239/8000000000000000000000000000 : ℝ)*base77 + (8513331243239/8000000000000000000000000000 : ℝ)*base79 + (10390234816761/4000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (6534841/5000000000000000000000 : ℝ)*base89 + (6534841/5000000000000000000000 : ℝ)*base91 + (6534841/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1549_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12507/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1549_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1549_s1_0 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-223906633/1250000000 : ℝ)*x 0 + (5547106041/10000000000 : ℝ)*x 1 + (2557965813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223906633/1250000000 : ℝ)^4595 ≤ (2734868287333/25000000000000 : ℝ)^3571 := by
    have hnat : (223906633 : ℕ)^4595*25000000000000^3571 ≤ 2734868287333^3571*1250000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223906633 1250000000 2734868287333 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5547106041/10000000000 : ℝ)^4595 ≤ (46846419064059/100000000000000 : ℝ)^3571 := by
    have hnat : (5547106041 : ℕ)^4595*100000000000000^3571 ≤ 46846419064059^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547106041 10000000000 46846419064059 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2557965813/5000000000 : ℝ)^4595 ≤ (42214107767447/100000000000000 : ℝ)^3571 := by
    have hnat : (2557965813 : ℕ)^4595*100000000000000^3571 ≤ 42214107767447^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2557965813 5000000000 42214107767447 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223906633/1250000000 : ℝ), (5547106041/10000000000 : ℝ), (2557965813/5000000000 : ℝ)] ![(2734868287333/25000000000000 : ℝ), (46846419064059/100000000000000 : ℝ), (42214107767447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223906633/1250000000 : ℝ)|^4595 ≤ (2734868287333/25000000000000 : ℝ)^3571
        have hw : |(-223906633/1250000000 : ℝ)|=(223906633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5547106041/10000000000 : ℝ)|^4595 ≤ (46846419064059/100000000000000 : ℝ)^3571
        have hw : |(5547106041/10000000000 : ℝ)|=(5547106041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2557965813/5000000000 : ℝ)|^4595 ≤ (42214107767447/100000000000000 : ℝ)^3571
        have hw : |(2557965813/5000000000 : ℝ)|=(2557965813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s1_1 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690018939/5000000000 : ℝ)*x 0 + (-201730321/1000000000 : ℝ)*x 1 + (5115931003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690018939/5000000000 : ℝ)^4595 ≤ (11259700764193/25000000000000 : ℝ)^3571 := by
    have hnat : (2690018939 : ℕ)^4595*25000000000000^3571 ≤ 11259700764193^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690018939 5000000000 11259700764193 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201730321/1000000000 : ℝ)^4595 ≤ (637354788933/5000000000000 : ℝ)^3571 := by
    have hnat : (201730321 : ℕ)^4595*5000000000000^3571 ≤ 637354788933^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201730321 1000000000 637354788933 5000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5115931003/10000000000 : ℝ)^4595 ≤ (5276762644081/12500000000000 : ℝ)^3571 := by
    have hnat : (5115931003 : ℕ)^4595*12500000000000^3571 ≤ 5276762644081^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115931003 10000000000 5276762644081 12500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690018939/5000000000 : ℝ), (-201730321/1000000000 : ℝ), (5115931003/10000000000 : ℝ)] ![(11259700764193/25000000000000 : ℝ), (637354788933/5000000000000 : ℝ), (5276762644081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690018939/5000000000 : ℝ)|^4595 ≤ (11259700764193/25000000000000 : ℝ)^3571
        have hw : |(2690018939/5000000000 : ℝ)|=(2690018939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201730321/1000000000 : ℝ)|^4595 ≤ (637354788933/5000000000000 : ℝ)^3571
        have hw : |(-201730321/1000000000 : ℝ)|=(201730321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5115931003/10000000000 : ℝ)|^4595 ≤ (5276762644081/12500000000000 : ℝ)^3571
        have hw : |(5115931003/10000000000 : ℝ)|=(5115931003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s1_2 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380037679/10000000000 : ℝ)*x 0 + (5115931123/10000000000 : ℝ)*x 1 + (-2017303317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380037679/10000000000 : ℝ)^4595 ≤ (2251940045657/5000000000000 : ℝ)^3571 := by
    have hnat : (5380037679 : ℕ)^4595*5000000000000^3571 ≤ 2251940045657^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380037679 10000000000 2251940045657 5000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5115931123/10000000000 : ℝ)^4595 ≤ (42214102426767/100000000000000 : ℝ)^3571 := by
    have hnat : (5115931123 : ℕ)^4595*100000000000000^3571 ≤ 42214102426767^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115931123 10000000000 42214102426767 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017303317/10000000000 : ℝ)^4595 ≤ (637354832433/5000000000000 : ℝ)^3571 := by
    have hnat : (2017303317 : ℕ)^4595*5000000000000^3571 ≤ 637354832433^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017303317 10000000000 637354832433 5000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380037679/10000000000 : ℝ), (5115931123/10000000000 : ℝ), (-2017303317/10000000000 : ℝ)] ![(2251940045657/5000000000000 : ℝ), (42214102426767/100000000000000 : ℝ), (637354832433/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380037679/10000000000 : ℝ)|^4595 ≤ (2251940045657/5000000000000 : ℝ)^3571
        have hw : |(5380037679/10000000000 : ℝ)|=(5380037679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5115931123/10000000000 : ℝ)|^4595 ≤ (42214102426767/100000000000000 : ℝ)^3571
        have hw : |(5115931123/10000000000 : ℝ)|=(5115931123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2017303317/10000000000 : ℝ)|^4595 ≤ (637354832433/5000000000000 : ℝ)^3571
        have hw : |(-2017303317/10000000000 : ℝ)|=(2017303317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s1_3 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118055221/5000000000 : ℝ)*x 0 + (375881989/1000000000 : ℝ)*x 1 + (297630599/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118055221/5000000000 : ℝ)^4595 ≤ (16556498697601/50000000000000 : ℝ)^3571 := by
    have hnat : (2118055221 : ℕ)^4595*50000000000000^3571 ≤ 16556498697601^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118055221 5000000000 16556498697601 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375881989/1000000000 : ℝ)^4595 ≤ (14195989474269/50000000000000 : ℝ)^3571 := by
    have hnat : (375881989 : ℕ)^4595*50000000000000^3571 ≤ 14195989474269^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375881989 1000000000 14195989474269 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297630599/625000000 : ℝ)^4595 ≤ (3849502363431/10000000000000 : ℝ)^3571 := by
    have hnat : (297630599 : ℕ)^4595*10000000000000^3571 ≤ 3849502363431^3571*625000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297630599 625000000 3849502363431 10000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118055221/5000000000 : ℝ), (375881989/1000000000 : ℝ), (297630599/625000000 : ℝ)] ![(16556498697601/50000000000000 : ℝ), (14195989474269/50000000000000 : ℝ), (3849502363431/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118055221/5000000000 : ℝ)|^4595 ≤ (16556498697601/50000000000000 : ℝ)^3571
        have hw : |(2118055221/5000000000 : ℝ)|=(2118055221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(375881989/1000000000 : ℝ)|^4595 ≤ (14195989474269/50000000000000 : ℝ)^3571
        have hw : |(375881989/1000000000 : ℝ)|=(375881989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297630599/625000000 : ℝ)|^4595 ≤ (3849502363431/10000000000000 : ℝ)^3571
        have hw : |(297630599/625000000 : ℝ)|=(297630599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s1_4 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-223936733/1250000000 : ℝ)*x 0 + (5120509279/10000000000 : ℝ)*x 1 + (5542458111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223936733/1250000000 : ℝ)^4595 ≤ (5470682746429/50000000000000 : ℝ)^3571 := by
    have hnat : (223936733 : ℕ)^4595*50000000000000^3571 ≤ 5470682746429^3571*1250000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223936733 1250000000 5470682746429 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5120509279/10000000000 : ℝ)^4595 ≤ (21131358967507/50000000000000 : ℝ)^3571 := by
    have hnat : (5120509279 : ℕ)^4595*50000000000000^3571 ≤ 21131358967507^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5120509279 10000000000 21131358967507 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5542458111/10000000000 : ℝ)^4595 ≤ (5849489568909/12500000000000 : ℝ)^3571 := by
    have hnat : (5542458111 : ℕ)^4595*12500000000000^3571 ≤ 5849489568909^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5542458111 10000000000 5849489568909 12500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223936733/1250000000 : ℝ), (5120509279/10000000000 : ℝ), (5542458111/10000000000 : ℝ)] ![(5470682746429/50000000000000 : ℝ), (21131358967507/50000000000000 : ℝ), (5849489568909/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223936733/1250000000 : ℝ)|^4595 ≤ (5470682746429/50000000000000 : ℝ)^3571
        have hw : |(-223936733/1250000000 : ℝ)|=(223936733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5120509279/10000000000 : ℝ)|^4595 ≤ (21131358967507/50000000000000 : ℝ)^3571
        have hw : |(5120509279/10000000000 : ℝ)|=(5120509279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5542458111/10000000000 : ℝ)|^4595 ≤ (5849489568909/12500000000000 : ℝ)^3571
        have hw : |(5542458111/10000000000 : ℝ)|=(5542458111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s1_5 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265991263/10000000000 : ℝ)*x 0 + (-318155571/2000000000 : ℝ)*x 1 + (5542457899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265991263/10000000000 : ℝ)^4595 ≤ (43814043418279/100000000000000 : ℝ)^3571 := by
    have hnat : (5265991263 : ℕ)^4595*100000000000000^3571 ≤ 43814043418279^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265991263 10000000000 43814043418279 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318155571/2000000000 : ℝ)^4595 ≤ (46950211633/500000000000 : ℝ)^3571 := by
    have hnat : (318155571 : ℕ)^4595*500000000000^3571 ≤ 46950211633^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318155571 2000000000 46950211633 500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5542457899/10000000000 : ℝ)^4595 ≤ (46795914248043/100000000000000 : ℝ)^3571 := by
    have hnat : (5542457899 : ℕ)^4595*100000000000000^3571 ≤ 46795914248043^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5542457899 10000000000 46795914248043 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265991263/10000000000 : ℝ), (-318155571/2000000000 : ℝ), (5542457899/10000000000 : ℝ)] ![(43814043418279/100000000000000 : ℝ), (46950211633/500000000000 : ℝ), (46795914248043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265991263/10000000000 : ℝ)|^4595 ≤ (43814043418279/100000000000000 : ℝ)^3571
        have hw : |(5265991263/10000000000 : ℝ)|=(5265991263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-318155571/2000000000 : ℝ)|^4595 ≤ (46950211633/500000000000 : ℝ)^3571
        have hw : |(-318155571/2000000000 : ℝ)|=(318155571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5542457899/10000000000 : ℝ)|^4595 ≤ (46795914248043/100000000000000 : ℝ)^3571
        have hw : |(5542457899/10000000000 : ℝ)|=(5542457899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s1_6 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265992677/10000000000 : ℝ)*x 0 + (5542457657/10000000000 : ℝ)*x 1 + (-99423513/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265992677/10000000000 : ℝ)^4595 ≤ (2190702927831/5000000000000 : ℝ)^3571 := by
    have hnat : (5265992677 : ℕ)^4595*5000000000000^3571 ≤ 2190702927831^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265992677 10000000000 2190702927831 5000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5542457657/10000000000 : ℝ)^4595 ≤ (23397955809443/50000000000000 : ℝ)^3571 := by
    have hnat : (5542457657 : ℕ)^4595*50000000000000^3571 ≤ 23397955809443^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5542457657 10000000000 23397955809443 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99423513/625000000 : ℝ)^4595 ≤ (939002981689/10000000000000 : ℝ)^3571 := by
    have hnat : (99423513 : ℕ)^4595*10000000000000^3571 ≤ 939002981689^3571*625000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99423513 625000000 939002981689 10000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265992677/10000000000 : ℝ), (5542457657/10000000000 : ℝ), (-99423513/625000000 : ℝ)] ![(2190702927831/5000000000000 : ℝ), (23397955809443/50000000000000 : ℝ), (939002981689/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265992677/10000000000 : ℝ)|^4595 ≤ (2190702927831/5000000000000 : ℝ)^3571
        have hw : |(5265992677/10000000000 : ℝ)|=(5265992677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5542457657/10000000000 : ℝ)|^4595 ≤ (23397955809443/50000000000000 : ℝ)^3571
        have hw : |(5542457657/10000000000 : ℝ)|=(5542457657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99423513/625000000 : ℝ)|^4595 ≤ (939002981689/10000000000000 : ℝ)^3571
        have hw : |(-99423513/625000000 : ℝ)|=(99423513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s1_7 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236669503/10000000000 : ℝ)*x 0 + (950287183/2000000000 : ℝ)*x 1 + (3769634707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236669503/10000000000 : ℝ)^4595 ≤ (33118620734657/100000000000000 : ℝ)^3571 := by
    have hnat : (4236669503 : ℕ)^4595*100000000000000^3571 ≤ 33118620734657^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236669503 10000000000 33118620734657 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950287183/2000000000 : ℝ)^4595 ≤ (38384243345443/100000000000000 : ℝ)^3571 := by
    have hnat : (950287183 : ℕ)^4595*100000000000000^3571 ≤ 38384243345443^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950287183 2000000000 38384243345443 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3769634707/10000000000 : ℝ)^4595 ≤ (28497135899603/100000000000000 : ℝ)^3571 := by
    have hnat : (3769634707 : ℕ)^4595*100000000000000^3571 ≤ 28497135899603^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3769634707 10000000000 28497135899603 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236669503/10000000000 : ℝ), (950287183/2000000000 : ℝ), (3769634707/10000000000 : ℝ)] ![(33118620734657/100000000000000 : ℝ), (38384243345443/100000000000000 : ℝ), (28497135899603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236669503/10000000000 : ℝ)|^4595 ≤ (33118620734657/100000000000000 : ℝ)^3571
        have hw : |(4236669503/10000000000 : ℝ)|=(4236669503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(950287183/2000000000 : ℝ)|^4595 ≤ (38384243345443/100000000000000 : ℝ)^3571
        have hw : |(950287183/2000000000 : ℝ)|=(950287183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3769634707/10000000000 : ℝ)|^4595 ≤ (28497135899603/100000000000000 : ℝ)^3571
        have hw : |(3769634707/10000000000 : ℝ)|=(3769634707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1549_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12507/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4413/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17953/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12507/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12507/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12507/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12507/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12507/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12507/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (823/25000 : ℝ) ^ (4593/1024 : ℝ) ≤ (11200982554989/50000000000000000000 : ℝ) := by
    have hpowers : (823/25000 : ℝ)^4593 ≤ (11200982554989/50000000000000000000 : ℝ)^1024 := by
      have hnat : (823 : ℕ)^4593*50000000000000000000^1024 ≤ 11200982554989^1024*25000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        823 25000 11200982554989 50000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (823/25000 : ℝ)) (X := (11200982554989/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12507/50000 : ℝ) ^ (4593/1024 : ℝ) ≤ (199820403390158663/100000000000000000000 : ℝ) := by
    have hpowers : (12507/50000 : ℝ)^4593 ≤ (199820403390158663/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12507 : ℕ)^4593*100000000000000000000^1024 ≤ 199820403390158663^1024*50000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507 50000 199820403390158663 100000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12507/50000 : ℝ)) (X := (199820403390158663/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000011200982554989/25000000000000000000 : ℝ) ≤ (1000000099889433/1000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (25000011200982554989/25000000000000000000 : ℝ)^1024 ≤ (1000000099889433/1000000000000000 : ℝ)^4593 := by
      have hnat : (25000011200982554989 : ℕ)^1024*1000000000000000^4593 ≤ 1000000099889433^4593*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000011200982554989 25000000000000000000 1000000099889433 1000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000099889433/1000000000000000 : ℝ)) (X := (25000011200982554989/25000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100199842805355268641/100000000000000000000 : ℝ) ≤ (625278249959609/625000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (100199842805355268641/100000000000000000000 : ℝ)^1024 ≤ (625278249959609/625000000000000 : ℝ)^4593 := by
      have hnat : (100199842805355268641 : ℕ)^1024*625000000000000^4593 ≤ 625278249959609^4593*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100199842805355268641 100000000000000000000 625278249959609 625000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625278249959609/625000000000000 : ℝ)) (X := (100199842805355268641/100000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50199820403390158663/50000000000000000000 : ℝ) ≤ (5004451499906579/5000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (50199820403390158663/50000000000000000000 : ℝ)^1024 ≤ (5004451499906579/5000000000000000 : ℝ)^4593 := by
      have hnat : (50199820403390158663 : ℕ)^1024*5000000000000000^4593 ≤ 5004451499906579^4593*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50199820403390158663 50000000000000000000 5004451499906579 5000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004451499906579/5000000000000000 : ℝ)) (X := (50199820403390158663/50000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11200982554989/50000000000000000000 : ℝ) ≤ ((54297679077739463621/54305000000000000000 : ℝ)+2*(2225500229707/1086100000000000 : ℝ)*(823/25000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (54297679077739463621/54305000000000000000 : ℝ)+2*(2225500229707/1086100000000000 : ℝ)*(823/25000 : ℝ)=(1000000099889433/1000000000000000 : ℝ) by norm_num, show 1+2*(11200982554989/50000000000000000000 : ℝ)=(25000011200982554989/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(199820403390158663/100000000000000000000 : ℝ)+(11200982554989/50000000000000000000 : ℝ) ≤ ((54297679077739463621/54305000000000000000 : ℝ)+(2225500229707/1086100000000000 : ℝ)*((12507/50000 : ℝ)+(823/25000 : ℝ)))^(4593/1024 : ℝ) := by
    rw [show (54297679077739463621/54305000000000000000 : ℝ)+(2225500229707/1086100000000000 : ℝ)*((12507/50000 : ℝ)+(823/25000 : ℝ))=(625278249959609/625000000000000 : ℝ) by norm_num, show 1+(199820403390158663/100000000000000000000 : ℝ)+(11200982554989/50000000000000000000 : ℝ)=(100199842805355268641/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(199820403390158663/100000000000000000000 : ℝ) ≤ ((54297679077739463621/54305000000000000000 : ℝ)+2*(2225500229707/1086100000000000 : ℝ)*(12507/50000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (54297679077739463621/54305000000000000000 : ℝ)+2*(2225500229707/1086100000000000 : ℝ)*(12507/50000 : ℝ)=(5004451499906579/5000000000000000 : ℝ) by norm_num, show 1+2*(199820403390158663/100000000000000000000 : ℝ)=(50199820403390158663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54297679077739463621/54305000000000000000 : ℝ)*(X 1 0+X 2 0)+(2225500229707/1086100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (823/25000 : ℝ)) (hi := (12507/50000 : ℝ)) (c := (54297679077739463621/54305000000000000000 : ℝ)) (alpha := (2225500229707/1086100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54297679077739463621/54305000000000000000 : ℝ)*(X 0 1+X 2 1)+(2225500229707/1086100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (823/25000 : ℝ)) (hi := (12507/50000 : ℝ)) (c := (54297679077739463621/54305000000000000000 : ℝ)) (alpha := (2225500229707/1086100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54297679077739463621/54305000000000000000 : ℝ)*(X 0 2+X 1 2)+(2225500229707/1086100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (823/25000 : ℝ)) (hi := (12507/50000 : ℝ)) (c := (54297679077739463621/54305000000000000000 : ℝ)) (alpha := (2225500229707/1086100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-223906633/1250000000 : ℝ)*X 0 0+(5547106041/10000000000 : ℝ)*X 0 1+(2557965813/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2690018939/5000000000 : ℝ)*X 1 0+(-201730321/1000000000 : ℝ)*X 1 1+(5115931003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5380037679/10000000000 : ℝ)*X 2 0+(5115931123/10000000000 : ℝ)*X 2 1+(-2017303317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2118055221/5000000000 : ℝ)*X 0 0+(375881989/1000000000 : ℝ)*X 0 1+(297630599/625000000 : ℝ)*X 0 2+(2118055221/5000000000 : ℝ)*X 1 0+(375881989/1000000000 : ℝ)*X 1 1+(297630599/625000000 : ℝ)*X 1 2+(2118055221/5000000000 : ℝ)*X 2 0+(375881989/1000000000 : ℝ)*X 2 1+(297630599/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-223936733/1250000000 : ℝ)*X 0 0+(5120509279/10000000000 : ℝ)*X 0 1+(5542458111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5265991263/10000000000 : ℝ)*X 1 0+(-318155571/2000000000 : ℝ)*X 1 1+(5542457899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265992677/10000000000 : ℝ)*X 2 0+(5542457657/10000000000 : ℝ)*X 2 1+(-99423513/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4236669503/10000000000 : ℝ)*X 0 0+(950287183/2000000000 : ℝ)*X 0 1+(3769634707/10000000000 : ℝ)*X 0 2+(4236669503/10000000000 : ℝ)*X 1 0+(950287183/2000000000 : ℝ)*X 1 1+(3769634707/10000000000 : ℝ)*X 1 2+(4236669503/10000000000 : ℝ)*X 2 0+(950287183/2000000000 : ℝ)*X 2 1+(3769634707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2542566562391963156965605921/678812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10199083/12500000000000 : ℝ)*(base1) + (9930697/2500000000000 : ℝ)*(base19) + (274478117/100000000000000 : ℝ)*(base23) + (1880159/25000000000000 : ℝ)*(lower2) + (3888751/50000000000000 : ℝ)*(upper3) + (180079/800000000000 : ℝ)*(upper5) + (828997081516267/50000000000000 : ℝ)*(major0) + (828997081516267/50000000000000 : ℝ)*(major1) + (828997081516267/50000000000000 : ℝ)*(major2) + (2319247059130907/100000000000000 : ℝ)*(sp0) + (1159623290155181/50000000000000 : ℝ)*(sp1) + (1159622809367223/50000000000000 : ℝ)*(sp2) + (498370571040253/50000000000000 : ℝ)*(sp3) + (13554071/1250000000000 : ℝ)*(sp6) + (99674122367317/10000000000000 : ℝ)*(f.failure) + (2319246977538243/100000000000000 : ℝ)*(f.sum) + (9144682341341/27152500000000000000000000000 : ℝ)*base66 + (17974506252032077193/2715250000000000000000000000000000 : ℝ)*base68 + (16210790522906827193/2715250000000000000000000000000000 : ℝ)*base70 + (40719766637327193/2715250000000000000000000000000000 : ℝ)*base72 + (148839073850031/27152500000000000000000000000 : ℝ)*base74 + (7893601584657172807/2715250000000000000000000000000000 : ℝ)*base75 + (4337180284696827193/2715250000000000000000000000000000 : ℝ)*base78 + (411686643554827193/2715250000000000000000000000000000 : ℝ)*base80 + (17602054637309/6788125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3806531/500000000000000000000 : ℝ)*base89 + (3806531/500000000000000000000 : ℝ)*base91 + (3806531/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4412620087242662839204641849/543050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1095640979/100000000000000 : ℝ)*(base19) + (1002794157/50000000000000 : ℝ)*(base23) + (21324107/50000000000000 : ℝ)*(upper2) + (221740431/100000000000000 : ℝ)*(upper3) + (373864093/100000000000000 : ℝ)*(upper5) + (338849638254023/20000000000000 : ℝ)*(major0) + (338849638254023/20000000000000 : ℝ)*(major1) + (338849638254023/20000000000000 : ℝ)*(major2) + (634200911/12500000000000 : ℝ)*(sp1) + (13966414679/100000000000000 : ℝ)*(sp2) + (236995994731029/10000000000000 : ℝ)*(sp4) + (1184976889031011/50000000000000 : ℝ)*(sp5) + (74060749228353/3125000000000 : ℝ)*(sp6) + (254634041093951/25000000000000 : ℝ)*(sp7) + (254634041093951/25000000000000 : ℝ)*(f.failure) + (236995994731029/10000000000000 : ℝ)*(f.sum) + (19662537076311/10861000000000000000000000000 : ℝ)*base66 + (384435989148552717/1086100000000000000000000000000000 : ℝ)*base68 + (2390147772281352717/1086100000000000000000000000000000 : ℝ)*base70 + (2676093355290247283/1086100000000000000000000000000000 : ℝ)*base71 + (35643428779691/10861000000000000000000000000 : ℝ)*base73 + (1333914927098552717/1086100000000000000000000000000000 : ℝ)*base76 + (4555587046326052717/1086100000000000000000000000000000 : ℝ)*base78 + (6538214357149547283/1086100000000000000000000000000000 : ℝ)*base79 + (644083939689/678812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (24407/1250000000000000000000 : ℝ)*base90 + (24407/1250000000000000000000 : ℝ)*base92 + (24407/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1549_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12507/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4413/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17953/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1549_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1549_s2_0 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14154917/78125000 : ℝ)*x 0 + (5446964183/10000000000 : ℝ)*x 1 + (6503367/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14154917/78125000 : ℝ)^4595 ≤ (2220287199963/20000000000000 : ℝ)^3571 := by
    have hnat : (14154917 : ℕ)^4595*20000000000000^3571 ≤ 2220287199963^3571*78125000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14154917 78125000 2220287199963 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446964183/10000000000 : ℝ)^4595 ≤ (45761016641703/100000000000000 : ℝ)^3571 := by
    have hnat : (5446964183 : ℕ)^4595*100000000000000^3571 ≤ 45761016641703^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446964183 10000000000 45761016641703 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6503367/12500000 : ℝ)^4595 ≤ (21568773675541/50000000000000 : ℝ)^3571 := by
    have hnat : (6503367 : ℕ)^4595*50000000000000^3571 ≤ 21568773675541^3571*12500000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6503367 12500000 21568773675541 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14154917/78125000 : ℝ), (5446964183/10000000000 : ℝ), (6503367/12500000 : ℝ)] ![(2220287199963/20000000000000 : ℝ), (45761016641703/100000000000000 : ℝ), (21568773675541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14154917/78125000 : ℝ)|^4595 ≤ (2220287199963/20000000000000 : ℝ)^3571
        have hw : |(-14154917/78125000 : ℝ)|=(14154917/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446964183/10000000000 : ℝ)|^4595 ≤ (45761016641703/100000000000000 : ℝ)^3571
        have hw : |(5446964183/10000000000 : ℝ)|=(5446964183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6503367/12500000 : ℝ)|^4595 ≤ (21568773675541/50000000000000 : ℝ)^3571
        have hw : |(6503367/12500000 : ℝ)|=(6503367/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s2_1 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354316241/10000000000 : ℝ)*x 0 + (-1937324301/10000000000 : ℝ)*x 1 + (5202693773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354316241/10000000000 : ℝ)^4595 ≤ (22380959599661/50000000000000 : ℝ)^3571 := by
    have hnat : (5354316241 : ℕ)^4595*50000000000000^3571 ≤ 22380959599661^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354316241 10000000000 22380959599661 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1937324301/10000000000 : ℝ)^4595 ≤ (6050265788419/50000000000000 : ℝ)^3571 := by
    have hnat : (1937324301 : ℕ)^4595*50000000000000^3571 ≤ 6050265788419^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937324301 10000000000 6050265788419 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5202693773/10000000000 : ℝ)^4595 ≤ (2696096824801/6250000000000 : ℝ)^3571 := by
    have hnat : (5202693773 : ℕ)^4595*6250000000000^3571 ≤ 2696096824801^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202693773 10000000000 2696096824801 6250000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354316241/10000000000 : ℝ), (-1937324301/10000000000 : ℝ), (5202693773/10000000000 : ℝ)] ![(22380959599661/50000000000000 : ℝ), (6050265788419/50000000000000 : ℝ), (2696096824801/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354316241/10000000000 : ℝ)|^4595 ≤ (22380959599661/50000000000000 : ℝ)^3571
        have hw : |(5354316241/10000000000 : ℝ)|=(5354316241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1937324301/10000000000 : ℝ)|^4595 ≤ (6050265788419/50000000000000 : ℝ)^3571
        have hw : |(-1937324301/10000000000 : ℝ)|=(1937324301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5202693773/10000000000 : ℝ)|^4595 ≤ (2696096824801/6250000000000 : ℝ)^3571
        have hw : |(5202693773/10000000000 : ℝ)|=(5202693773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s2_2 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354316933/10000000000 : ℝ)*x 0 + (5202693191/10000000000 : ℝ)*x 1 + (-1937324149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354316933/10000000000 : ℝ)^4595 ≤ (44761926643323/100000000000000 : ℝ)^3571 := by
    have hnat : (5354316933 : ℕ)^4595*100000000000000^3571 ≤ 44761926643323^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354316933 10000000000 44761926643323 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202693191/10000000000 : ℝ)^4595 ≤ (4313754298747/10000000000000 : ℝ)^3571 := by
    have hnat : (5202693191 : ℕ)^4595*10000000000000^3571 ≤ 4313754298747^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202693191 10000000000 4313754298747 10000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1937324149/10000000000 : ℝ)^4595 ≤ (12100530355203/100000000000000 : ℝ)^3571 := by
    have hnat : (1937324149 : ℕ)^4595*100000000000000^3571 ≤ 12100530355203^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937324149 10000000000 12100530355203 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354316933/10000000000 : ℝ), (5202693191/10000000000 : ℝ), (-1937324149/10000000000 : ℝ)] ![(44761926643323/100000000000000 : ℝ), (4313754298747/10000000000000 : ℝ), (12100530355203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354316933/10000000000 : ℝ)|^4595 ≤ (44761926643323/100000000000000 : ℝ)^3571
        have hw : |(5354316933/10000000000 : ℝ)|=(5354316933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202693191/10000000000 : ℝ)|^4595 ≤ (4313754298747/10000000000000 : ℝ)^3571
        have hw : |(5202693191/10000000000 : ℝ)|=(5202693191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1937324149/10000000000 : ℝ)|^4595 ≤ (12100530355203/100000000000000 : ℝ)^3571
        have hw : |(-1937324149/10000000000 : ℝ)|=(1937324149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s2_3 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250973659/10000000000 : ℝ)*x 0 + (993650739/2500000000 : ℝ)*x 1 + (2271490481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250973659/10000000000 : ℝ)^4595 ≤ (665251440571/2000000000000 : ℝ)^3571 := by
    have hnat : (4250973659 : ℕ)^4595*2000000000000^3571 ≤ 665251440571^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250973659 10000000000 665251440571 2000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993650739/2500000000 : ℝ)^4595 ≤ (30506295098129/100000000000000 : ℝ)^3571 := by
    have hnat : (993650739 : ℕ)^4595*100000000000000^3571 ≤ 30506295098129^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993650739 2500000000 30506295098129 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271490481/5000000000 : ℝ)^4595 ≤ (36231132848157/100000000000000 : ℝ)^3571 := by
    have hnat : (2271490481 : ℕ)^4595*100000000000000^3571 ≤ 36231132848157^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271490481 5000000000 36231132848157 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250973659/10000000000 : ℝ), (993650739/2500000000 : ℝ), (2271490481/5000000000 : ℝ)] ![(665251440571/2000000000000 : ℝ), (30506295098129/100000000000000 : ℝ), (36231132848157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250973659/10000000000 : ℝ)|^4595 ≤ (665251440571/2000000000000 : ℝ)^3571
        have hw : |(4250973659/10000000000 : ℝ)|=(4250973659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993650739/2500000000 : ℝ)|^4595 ≤ (30506295098129/100000000000000 : ℝ)^3571
        have hw : |(993650739/2500000000 : ℝ)|=(993650739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2271490481/5000000000 : ℝ)|^4595 ≤ (36231132848157/100000000000000 : ℝ)^3571
        have hw : |(2271490481/5000000000 : ℝ)|=(2271490481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s2_4 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1811872461/10000000000 : ℝ)*x 0 + (162630341/312500000 : ℝ)*x 1 + (5445474639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811872461/10000000000 : ℝ)^4595 ≤ (11101775691649/100000000000000 : ℝ)^3571 := by
    have hnat : (1811872461 : ℕ)^4595*100000000000000^3571 ≤ 11101775691649^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811872461 10000000000 11101775691649 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162630341/312500000 : ℝ)^4595 ≤ (43153309403581/100000000000000 : ℝ)^3571 := by
    have hnat : (162630341 : ℕ)^4595*100000000000000^3571 ≤ 43153309403581^3571*312500000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162630341 312500000 43153309403581 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445474639/10000000000 : ℝ)^4595 ≤ (9148982978059/20000000000000 : ℝ)^3571 := by
    have hnat : (5445474639 : ℕ)^4595*20000000000000^3571 ≤ 9148982978059^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445474639 10000000000 9148982978059 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1811872461/10000000000 : ℝ), (162630341/312500000 : ℝ), (5445474639/10000000000 : ℝ)] ![(11101775691649/100000000000000 : ℝ), (43153309403581/100000000000000 : ℝ), (9148982978059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1811872461/10000000000 : ℝ)|^4595 ≤ (11101775691649/100000000000000 : ℝ)^3571
        have hw : |(-1811872461/10000000000 : ℝ)|=(1811872461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162630341/312500000 : ℝ)|^4595 ≤ (43153309403581/100000000000000 : ℝ)^3571
        have hw : |(162630341/312500000 : ℝ)|=(162630341/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445474639/10000000000 : ℝ)|^4595 ≤ (9148982978059/20000000000000 : ℝ)^3571
        have hw : |(5445474639/10000000000 : ℝ)|=(5445474639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s2_5 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528984989/1000000000 : ℝ)*x 0 + (-1694543177/10000000000 : ℝ)*x 1 + (544547443/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528984989/1000000000 : ℝ)^4595 ≤ (22034820292617/50000000000000 : ℝ)^3571 := by
    have hnat : (528984989 : ℕ)^4595*50000000000000^3571 ≤ 22034820292617^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528984989 1000000000 22034820292617 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1694543177/10000000000 : ℝ)^4595 ≤ (2546361690623/25000000000000 : ℝ)^3571 := by
    have hnat : (1694543177 : ℕ)^4595*25000000000000^3571 ≤ 2546361690623^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694543177 10000000000 2546361690623 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544547443/1000000000 : ℝ)^4595 ≤ (365959301049/800000000000 : ℝ)^3571 := by
    have hnat : (544547443 : ℕ)^4595*800000000000^3571 ≤ 365959301049^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544547443 1000000000 365959301049 800000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528984989/1000000000 : ℝ), (-1694543177/10000000000 : ℝ), (544547443/1000000000 : ℝ)] ![(22034820292617/50000000000000 : ℝ), (2546361690623/25000000000000 : ℝ), (365959301049/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528984989/1000000000 : ℝ)|^4595 ≤ (22034820292617/50000000000000 : ℝ)^3571
        have hw : |(528984989/1000000000 : ℝ)|=(528984989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1694543177/10000000000 : ℝ)|^4595 ≤ (2546361690623/25000000000000 : ℝ)^3571
        have hw : |(-1694543177/10000000000 : ℝ)|=(1694543177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544547443/1000000000 : ℝ)|^4595 ≤ (365959301049/800000000000 : ℝ)^3571
        have hw : |(544547443/1000000000 : ℝ)|=(544547443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s2_6 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211593981/400000000 : ℝ)*x 0 + (680684331/1250000000 : ℝ)*x 1 + (-1694543379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211593981/400000000 : ℝ)^4595 ≤ (44069636672461/100000000000000 : ℝ)^3571 := by
    have hnat : (211593981 : ℕ)^4595*100000000000000^3571 ≤ 44069636672461^3571*400000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211593981 400000000 44069636672461 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680684331/1250000000 : ℝ)^4595 ≤ (2287245749379/5000000000000 : ℝ)^3571 := by
    have hnat : (680684331 : ℕ)^4595*5000000000000^3571 ≤ 2287245749379^3571*1250000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680684331 1250000000 2287245749379 5000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1694543379/10000000000 : ℝ)^4595 ≤ (2546362081207/25000000000000 : ℝ)^3571 := by
    have hnat : (1694543379 : ℕ)^4595*25000000000000^3571 ≤ 2546362081207^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694543379 10000000000 2546362081207 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211593981/400000000 : ℝ), (680684331/1250000000 : ℝ), (-1694543379/10000000000 : ℝ)] ![(44069636672461/100000000000000 : ℝ), (2287245749379/5000000000000 : ℝ), (2546362081207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211593981/400000000 : ℝ)|^4595 ≤ (44069636672461/100000000000000 : ℝ)^3571
        have hw : |(211593981/400000000 : ℝ)|=(211593981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680684331/1250000000 : ℝ)|^4595 ≤ (2287245749379/5000000000000 : ℝ)^3571
        have hw : |(680684331/1250000000 : ℝ)|=(680684331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1694543379/10000000000 : ℝ)|^4595 ≤ (2546362081207/25000000000000 : ℝ)^3571
        have hw : |(-1694543379/10000000000 : ℝ)|=(1694543379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s2_7 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425107471/1000000000 : ℝ)*x 0 + (2269771331/5000000000 : ℝ)*x 1 + (994517939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425107471/1000000000 : ℝ)^4595 ≤ (33263589460041/100000000000000 : ℝ)^3571 := by
    have hnat : (425107471 : ℕ)^4595*100000000000000^3571 ≤ 33263589460041^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425107471 1000000000 33263589460041 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269771331/5000000000 : ℝ)^4595 ≤ (36195852465119/100000000000000 : ℝ)^3571 := by
    have hnat : (2269771331 : ℕ)^4595*100000000000000^3571 ≤ 36195852465119^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269771331 5000000000 36195852465119 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994517939/2500000000 : ℝ)^4595 ≤ (30540558065369/100000000000000 : ℝ)^3571 := by
    have hnat : (994517939 : ℕ)^4595*100000000000000^3571 ≤ 30540558065369^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994517939 2500000000 30540558065369 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425107471/1000000000 : ℝ), (2269771331/5000000000 : ℝ), (994517939/2500000000 : ℝ)] ![(33263589460041/100000000000000 : ℝ), (36195852465119/100000000000000 : ℝ), (30540558065369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425107471/1000000000 : ℝ)|^4595 ≤ (33263589460041/100000000000000 : ℝ)^3571
        have hw : |(425107471/1000000000 : ℝ)|=(425107471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2269771331/5000000000 : ℝ)|^4595 ≤ (36195852465119/100000000000000 : ℝ)^3571
        have hw : |(2269771331/5000000000 : ℝ)|=(2269771331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(994517939/2500000000 : ℝ)|^4595 ≤ (30540558065369/100000000000000 : ℝ)^3571
        have hw : |(994517939/2500000000 : ℝ)|=(994517939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1549_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17953/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4413/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2139/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15871/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17953/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4413/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17953/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4413/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17953/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4413/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17953/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4413/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17953/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4413/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17953/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4413/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4413/50000 : ℝ) ^ (4593/1024 : ℝ) ≤ (233501985772277/12500000000000000000 : ℝ) := by
    have hpowers : (4413/50000 : ℝ)^4593 ≤ (233501985772277/12500000000000000000 : ℝ)^1024 := by
      have hnat : (4413 : ℕ)^4593*12500000000000000000^1024 ≤ 233501985772277^1024*50000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4413 50000 233501985772277 12500000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4413/50000 : ℝ)) (X := (233501985772277/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17953/100000 : ℝ) ^ (4593/1024 : ℝ) ≤ (22569002799382341/50000000000000000000 : ℝ) := by
    have hpowers : (17953/100000 : ℝ)^4593 ≤ (22569002799382341/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17953 : ℕ)^4593*50000000000000000000^1024 ≤ 22569002799382341^1024*100000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17953 100000 22569002799382341 50000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17953/100000 : ℝ)) (X := (22569002799382341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250233501985772277/6250000000000000000 : ℝ) ≤ (5000041646429397/5000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (6250233501985772277/6250000000000000000 : ℝ)^1024 ≤ (5000041646429397/5000000000000000 : ℝ)^4593 := by
      have hnat : (6250233501985772277 : ℕ)^1024*5000000000000000^4593 ≤ 5000041646429397^4593*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250233501985772277 6250000000000000000 5000041646429397 5000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000041646429397/5000000000000000 : ℝ)) (X := (6250233501985772277/6250000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023503010742471449/50000000000000000000 : ℝ) ≤ (10001047798338227/10000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (50023503010742471449/50000000000000000000 : ℝ)^1024 ≤ (10001047798338227/10000000000000000 : ℝ)^4593 := by
      have hnat : (50023503010742471449 : ℕ)^1024*10000000000000000^4593 ≤ 10001047798338227^4593*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023503010742471449 50000000000000000000 10001047798338227 10000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001047798338227/10000000000000000 : ℝ)) (X := (50023503010742471449/50000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022569002799382341/25000000000000000000 : ℝ) ≤ (500100615190883/500000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (25022569002799382341/25000000000000000000 : ℝ)^1024 ≤ (500100615190883/500000000000000 : ℝ)^4593 := by
      have hnat : (25022569002799382341 : ℕ)^1024*500000000000000^4593 ≤ 500100615190883^4593*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022569002799382341 25000000000000000000 500100615190883 500000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500100615190883/500000000000000 : ℝ)) (X := (25022569002799382341/25000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(233501985772277/12500000000000000000 : ℝ) ≤ ((45626867381599630761/45635000000000000000 : ℝ)+2*(964505479433/912700000000000 : ℝ)*(4413/50000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (45626867381599630761/45635000000000000000 : ℝ)+2*(964505479433/912700000000000 : ℝ)*(4413/50000 : ℝ)=(5000041646429397/5000000000000000 : ℝ) by norm_num, show 1+2*(233501985772277/12500000000000000000 : ℝ)=(6250233501985772277/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22569002799382341/50000000000000000000 : ℝ)+(233501985772277/12500000000000000000 : ℝ) ≤ ((45626867381599630761/45635000000000000000 : ℝ)+(964505479433/912700000000000 : ℝ)*((17953/100000 : ℝ)+(4413/50000 : ℝ)))^(4593/1024 : ℝ) := by
    rw [show (45626867381599630761/45635000000000000000 : ℝ)+(964505479433/912700000000000 : ℝ)*((17953/100000 : ℝ)+(4413/50000 : ℝ))=(10001047798338227/10000000000000000 : ℝ) by norm_num, show 1+(22569002799382341/50000000000000000000 : ℝ)+(233501985772277/12500000000000000000 : ℝ)=(50023503010742471449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22569002799382341/50000000000000000000 : ℝ) ≤ ((45626867381599630761/45635000000000000000 : ℝ)+2*(964505479433/912700000000000 : ℝ)*(17953/100000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (45626867381599630761/45635000000000000000 : ℝ)+2*(964505479433/912700000000000 : ℝ)*(17953/100000 : ℝ)=(500100615190883/500000000000000 : ℝ) by norm_num, show 1+2*(22569002799382341/50000000000000000000 : ℝ)=(25022569002799382341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45626867381599630761/45635000000000000000 : ℝ)*(X 1 0+X 2 0)+(964505479433/912700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (4413/50000 : ℝ)) (hi := (17953/100000 : ℝ)) (c := (45626867381599630761/45635000000000000000 : ℝ)) (alpha := (964505479433/912700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45626867381599630761/45635000000000000000 : ℝ)*(X 0 1+X 2 1)+(964505479433/912700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (4413/50000 : ℝ)) (hi := (17953/100000 : ℝ)) (c := (45626867381599630761/45635000000000000000 : ℝ)) (alpha := (964505479433/912700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45626867381599630761/45635000000000000000 : ℝ)*(X 0 2+X 1 2)+(964505479433/912700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (4413/50000 : ℝ)) (hi := (17953/100000 : ℝ)) (c := (45626867381599630761/45635000000000000000 : ℝ)) (alpha := (964505479433/912700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-14154917/78125000 : ℝ)*X 0 0+(5446964183/10000000000 : ℝ)*X 0 1+(6503367/12500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354316241/10000000000 : ℝ)*X 1 0+(-1937324301/10000000000 : ℝ)*X 1 1+(5202693773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354316933/10000000000 : ℝ)*X 2 0+(5202693191/10000000000 : ℝ)*X 2 1+(-1937324149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4250973659/10000000000 : ℝ)*X 0 0+(993650739/2500000000 : ℝ)*X 0 1+(2271490481/5000000000 : ℝ)*X 0 2+(4250973659/10000000000 : ℝ)*X 1 0+(993650739/2500000000 : ℝ)*X 1 1+(2271490481/5000000000 : ℝ)*X 1 2+(4250973659/10000000000 : ℝ)*X 2 0+(993650739/2500000000 : ℝ)*X 2 1+(2271490481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1811872461/10000000000 : ℝ)*X 0 0+(162630341/312500000 : ℝ)*X 0 1+(5445474639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528984989/1000000000 : ℝ)*X 1 0+(-1694543177/10000000000 : ℝ)*X 1 1+(544547443/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211593981/400000000 : ℝ)*X 2 0+(680684331/1250000000 : ℝ)*X 2 1+(-1694543379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((425107471/1000000000 : ℝ)*X 0 0+(2269771331/5000000000 : ℝ)*X 0 1+(994517939/2500000000 : ℝ)*X 0 2+(425107471/1000000000 : ℝ)*X 1 0+(2269771331/5000000000 : ℝ)*X 1 1+(994517939/2500000000 : ℝ)*X 1 2+(425107471/1000000000 : ℝ)*X 2 0+(2269771331/5000000000 : ℝ)*X 2 1+(994517939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1849778795181547022238356403/228175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1097454849/50000000000000 : ℝ)*(base19) + (588107453/25000000000000 : ℝ)*(base23) + (317326259/100000000000000 : ℝ)*(upper3) + (198955213/100000000000000 : ℝ)*(upper4) + (275600889/100000000000000 : ℝ)*(upper5) + (292665354444453/10000000000000 : ℝ)*(major0) + (292665354444453/10000000000000 : ℝ)*(major1) + (292665354444453/10000000000000 : ℝ)*(major2) + (1023462172119209/25000000000000 : ℝ)*(sp0) + (4093879711288641/100000000000000 : ℝ)*(sp1) + (2046939776884263/50000000000000 : ℝ)*(sp2) + (879703708095631/50000000000000 : ℝ)*(sp3) + (16608860751/50000000000000 : ℝ)*(sp4) + (17496271363/100000000000000 : ℝ)*(sp7) + (14075399299701/800000000000 : ℝ)*(f.failure) + (4093881906198339/100000000000000 : ℝ)*(f.sum) + (739073672393/570437500000000000000000000 : ℝ)*base65 + (9170355499045568733/456350000000000000000000000000000 : ℝ)*base67 + (4864354975044568733/456350000000000000000000000000000 : ℝ)*base69 + (6831177375023918733/456350000000000000000000000000000 : ℝ)*base71 + (33487317319999/9127000000000000000000000000 : ℝ)*base73 + (1476004089314318733/456350000000000000000000000000000 : ℝ)*base75 + (1729580360414968733/456350000000000000000000000000000 : ℝ)*base77 + (7131478777742668733/456350000000000000000000000000000 : ℝ)*base79 + (6832267846287/2281750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (152157/40000000000000000000 : ℝ)*base90 + (152157/40000000000000000000 : ℝ)*base92 + (152157/40000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8517777943371358826054144193/1140875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138428547/12500000000000 : ℝ)*(base19) + (885870867/100000000000000 : ℝ)*(base23) + (15870951/25000000000000 : ℝ)*(upper2) + (47779911/50000000000000 : ℝ)*(upper5) + (1481299457331229/50000000000000 : ℝ)*(major0) + (1481299457331229/50000000000000 : ℝ)*(major1) + (1481299457331229/50000000000000 : ℝ)*(major2) + (4309547919/100000000000000 : ℝ)*(sp0) + (21517188873/100000000000000 : ℝ)*(sp1) + (16952906243/100000000000000 : ℝ)*(sp2) + (2072079487296853/50000000000000 : ℝ)*(sp4) + (6630625055239/160000000000 : ℝ)*(sp5) + (2072072722682257/50000000000000 : ℝ)*(sp6) + (1781034296316469/100000000000000 : ℝ)*(sp7) + (1781034296316469/100000000000000 : ℝ)*(f.failure) + (518020410517703/12500000000000 : ℝ)*(f.sum) + (15115787569507/22817500000000000000000000000 : ℝ)*base65 + (4567429624700064731/2281750000000000000000000000000000 : ℝ)*base68 + (7991023389579314731/2281750000000000000000000000000000 : ℝ)*base70 + (7341734148559435269/2281750000000000000000000000000000 : ℝ)*base71 + (13598017040809/11408750000000000000000000000 : ℝ)*base74 + (6567503265366935269/2281750000000000000000000000000000 : ℝ)*base75 + (1918896463783935269/2281750000000000000000000000000000 : ℝ)*base77 + (25723560453206935269/2281750000000000000000000000000000 : ℝ)*base79 + (12144846991429/45635000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (10133533/5000000000000000000000 : ℝ)*base90 + (10133533/5000000000000000000000 : ℝ)*base92 + (10133533/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1549_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17953/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4413/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15871/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1549_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1549_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15871/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1549_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1549_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1549_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15871/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1549_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
