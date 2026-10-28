-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1037_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:44:27.690404+00:00
-- url     : https://prove2.me/submissions/99779e46-984f-4dc2-bba4-f7915a319292

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
theorem support_rectangle_w1037_s6_0 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-110903569/500000000 : ℝ)*x 0 + (5395511467/10000000000 : ℝ)*x 1 + (42106341/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110903569/500000000 : ℝ)^4115 ≤ (13468133948853/100000000000000 : ℝ)^3091 := by
    have hnat : (110903569 : ℕ)^4115*100000000000000^3091 ≤ 13468133948853^3091*500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110903569 500000000 13468133948853 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395511467/10000000000 : ℝ)^4115 ≤ (43980403966349/100000000000000 : ℝ)^3091 := by
    have hnat : (5395511467 : ℕ)^4115*100000000000000^3091 ≤ 43980403966349^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395511467 10000000000 43980403966349 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42106341/80000000 : ℝ)^4115 ≤ (42551462073031/100000000000000 : ℝ)^3091 := by
    have hnat : (42106341 : ℕ)^4115*100000000000000^3091 ≤ 42551462073031^3091*80000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42106341 80000000 42551462073031 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110903569/500000000 : ℝ), (5395511467/10000000000 : ℝ), (42106341/80000000 : ℝ)] ![(13468133948853/100000000000000 : ℝ), (43980403966349/100000000000000 : ℝ), (42551462073031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110903569/500000000 : ℝ)|^4115 ≤ (13468133948853/100000000000000 : ℝ)^3091
        have hw : |(-110903569/500000000 : ℝ)|=(110903569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395511467/10000000000 : ℝ)|^4115 ≤ (43980403966349/100000000000000 : ℝ)^3091
        have hw : |(5395511467/10000000000 : ℝ)|=(5395511467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42106341/80000000 : ℝ)|^4115 ≤ (42551462073031/100000000000000 : ℝ)^3091
        have hw : |(42106341/80000000 : ℝ)|=(42106341/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s6_1 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668149989/1250000000 : ℝ)*x 0 + (-1142586571/5000000000 : ℝ)*x 1 + (5263292551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668149989/1250000000 : ℝ)^4115 ≤ (2171764177193/5000000000000 : ℝ)^3091 := by
    have hnat : (668149989 : ℕ)^4115*5000000000000^3091 ≤ 2171764177193^3091*1250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668149989 1250000000 2171764177193 5000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142586571/5000000000 : ℝ)^4115 ≤ (14013255166703/100000000000000 : ℝ)^3091 := by
    have hnat : (1142586571 : ℕ)^4115*100000000000000^3091 ≤ 14013255166703^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142586571 5000000000 14013255166703 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263292551/10000000000 : ℝ)^4115 ≤ (42551461276579/100000000000000 : ℝ)^3091 := by
    have hnat : (5263292551 : ℕ)^4115*100000000000000^3091 ≤ 42551461276579^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263292551 10000000000 42551461276579 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668149989/1250000000 : ℝ), (-1142586571/5000000000 : ℝ), (5263292551/10000000000 : ℝ)] ![(2171764177193/5000000000000 : ℝ), (14013255166703/100000000000000 : ℝ), (42551461276579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668149989/1250000000 : ℝ)|^4115 ≤ (2171764177193/5000000000000 : ℝ)^3091
        have hw : |(668149989/1250000000 : ℝ)|=(668149989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1142586571/5000000000 : ℝ)|^4115 ≤ (14013255166703/100000000000000 : ℝ)^3091
        have hw : |(-1142586571/5000000000 : ℝ)|=(1142586571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263292551/10000000000 : ℝ)|^4115 ≤ (42551461276579/100000000000000 : ℝ)^3091
        have hw : |(5263292551/10000000000 : ℝ)|=(5263292551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s6_2 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534519981/1000000000 : ℝ)*x 0 + (5263292631/10000000000 : ℝ)*x 1 + (-571293293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534519981/1000000000 : ℝ)^4115 ≤ (21717641220209/50000000000000 : ℝ)^3091 := by
    have hnat : (534519981 : ℕ)^4115*50000000000000^3091 ≤ 21717641220209^3091*1000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534519981 1000000000 21717641220209 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263292631/10000000000 : ℝ)^4115 ≤ (5318932767201/12500000000000 : ℝ)^3091 := by
    have hnat : (5263292631 : ℕ)^4115*12500000000000^3091 ≤ 5318932767201^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263292631 10000000000 5318932767201 12500000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571293293/2500000000 : ℝ)^4115 ≤ (437914231613/3125000000000 : ℝ)^3091 := by
    have hnat : (571293293 : ℕ)^4115*3125000000000^3091 ≤ 437914231613^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571293293 2500000000 437914231613 3125000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534519981/1000000000 : ℝ), (5263292631/10000000000 : ℝ), (-571293293/2500000000 : ℝ)] ![(21717641220209/50000000000000 : ℝ), (5318932767201/12500000000000 : ℝ), (437914231613/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534519981/1000000000 : ℝ)|^4115 ≤ (21717641220209/50000000000000 : ℝ)^3091
        have hw : |(534519981/1000000000 : ℝ)|=(534519981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263292631/10000000000 : ℝ)|^4115 ≤ (5318932767201/12500000000000 : ℝ)^3091
        have hw : |(5263292631/10000000000 : ℝ)|=(5263292631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-571293293/2500000000 : ℝ)|^4115 ≤ (437914231613/3125000000000 : ℝ)^3091
        have hw : |(-571293293/2500000000 : ℝ)|=(571293293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s6_3 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218982301/500000000 : ℝ)*x 0 + (4252760889/10000000000 : ℝ)*x 1 + (2255199593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218982301/500000000 : ℝ)^4115 ≤ (416450483501/1250000000000 : ℝ)^3091 := by
    have hnat : (218982301 : ℕ)^4115*1250000000000^3091 ≤ 416450483501^3091*500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218982301 500000000 416450483501 1250000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252760889/10000000000 : ℝ)^4115 ≤ (32037266833519/100000000000000 : ℝ)^3091 := by
    have hnat : (4252760889 : ℕ)^4115*100000000000000^3091 ≤ 32037266833519^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252760889 10000000000 32037266833519 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255199593/5000000000 : ℝ)^4115 ≤ (34646694472639/100000000000000 : ℝ)^3091 := by
    have hnat : (2255199593 : ℕ)^4115*100000000000000^3091 ≤ 34646694472639^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255199593 5000000000 34646694472639 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218982301/500000000 : ℝ), (4252760889/10000000000 : ℝ), (2255199593/5000000000 : ℝ)] ![(416450483501/1250000000000 : ℝ), (32037266833519/100000000000000 : ℝ), (34646694472639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218982301/500000000 : ℝ)|^4115 ≤ (416450483501/1250000000000 : ℝ)^3091
        have hw : |(218982301/500000000 : ℝ)|=(218982301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252760889/10000000000 : ℝ)|^4115 ≤ (32037266833519/100000000000000 : ℝ)^3091
        have hw : |(4252760889/10000000000 : ℝ)|=(4252760889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255199593/5000000000 : ℝ)|^4115 ≤ (34646694472639/100000000000000 : ℝ)^3091
        have hw : |(2255199593/5000000000 : ℝ)|=(2255199593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s6_4 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1109038719/5000000000 : ℝ)*x 0 + (5263626587/10000000000 : ℝ)*x 1 + (5395175719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109038719/5000000000 : ℝ)^4115 ≤ (1346818291909/10000000000000 : ℝ)^3091 := by
    have hnat : (1109038719 : ℕ)^4115*10000000000000^3091 ≤ 1346818291909^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109038719 5000000000 1346818291909 10000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263626587/10000000000 : ℝ)^4115 ≤ (10638764124501/25000000000000 : ℝ)^3091 := by
    have hnat : (5263626587 : ℕ)^4115*25000000000000^3091 ≤ 10638764124501^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263626587 10000000000 10638764124501 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395175719/10000000000 : ℝ)^4115 ≤ (43976760570271/100000000000000 : ℝ)^3091 := by
    have hnat : (5395175719 : ℕ)^4115*100000000000000^3091 ≤ 43976760570271^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395175719 10000000000 43976760570271 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1109038719/5000000000 : ℝ), (5263626587/10000000000 : ℝ), (5395175719/10000000000 : ℝ)] ![(1346818291909/10000000000000 : ℝ), (10638764124501/25000000000000 : ℝ), (43976760570271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1109038719/5000000000 : ℝ)|^4115 ≤ (1346818291909/10000000000000 : ℝ)^3091
        have hw : |(-1109038719/5000000000 : ℝ)|=(1109038719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263626587/10000000000 : ℝ)|^4115 ≤ (10638764124501/25000000000000 : ℝ)^3091
        have hw : |(5263626587/10000000000 : ℝ)|=(5263626587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395175719/10000000000 : ℝ)|^4115 ≤ (43976760570271/100000000000000 : ℝ)^3091
        have hw : |(5395175719/10000000000 : ℝ)|=(5395175719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s6_5 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265598727/500000000 : ℝ)*x 0 + (-1076644983/5000000000 : ℝ)*x 1 + (5395175719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265598727/500000000 : ℝ)^4115 ≤ (43076219940763/100000000000000 : ℝ)^3091 := by
    have hnat : (265598727 : ℕ)^4115*100000000000000^3091 ≤ 43076219940763^3091*500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265598727 500000000 43076219940763 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076644983/5000000000 : ℝ)^4115 ≤ (12947019478069/100000000000000 : ℝ)^3091 := by
    have hnat : (1076644983 : ℕ)^4115*100000000000000^3091 ≤ 12947019478069^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076644983 5000000000 12947019478069 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395175719/10000000000 : ℝ)^4115 ≤ (43976760570271/100000000000000 : ℝ)^3091 := by
    have hnat : (5395175719 : ℕ)^4115*100000000000000^3091 ≤ 43976760570271^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395175719 10000000000 43976760570271 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265598727/500000000 : ℝ), (-1076644983/5000000000 : ℝ), (5395175719/10000000000 : ℝ)] ![(43076219940763/100000000000000 : ℝ), (12947019478069/100000000000000 : ℝ), (43976760570271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265598727/500000000 : ℝ)|^4115 ≤ (43076219940763/100000000000000 : ℝ)^3091
        have hw : |(265598727/500000000 : ℝ)|=(265598727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076644983/5000000000 : ℝ)|^4115 ≤ (12947019478069/100000000000000 : ℝ)^3091
        have hw : |(-1076644983/5000000000 : ℝ)|=(1076644983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395175719/10000000000 : ℝ)|^4115 ≤ (43976760570271/100000000000000 : ℝ)^3091
        have hw : |(5395175719/10000000000 : ℝ)|=(5395175719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s6_6 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265598727/500000000 : ℝ)*x 0 + (5395175719/10000000000 : ℝ)*x 1 + (-1076644983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265598727/500000000 : ℝ)^4115 ≤ (43076219940763/100000000000000 : ℝ)^3091 := by
    have hnat : (265598727 : ℕ)^4115*100000000000000^3091 ≤ 43076219940763^3091*500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265598727 500000000 43076219940763 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395175719/10000000000 : ℝ)^4115 ≤ (43976760570271/100000000000000 : ℝ)^3091 := by
    have hnat : (5395175719 : ℕ)^4115*100000000000000^3091 ≤ 43976760570271^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395175719 10000000000 43976760570271 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076644983/5000000000 : ℝ)^4115 ≤ (12947019478069/100000000000000 : ℝ)^3091 := by
    have hnat : (1076644983 : ℕ)^4115*100000000000000^3091 ≤ 12947019478069^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076644983 5000000000 12947019478069 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265598727/500000000 : ℝ), (5395175719/10000000000 : ℝ), (-1076644983/5000000000 : ℝ)] ![(43076219940763/100000000000000 : ℝ), (43976760570271/100000000000000 : ℝ), (12947019478069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265598727/500000000 : ℝ)|^4115 ≤ (43076219940763/100000000000000 : ℝ)^3091
        have hw : |(265598727/500000000 : ℝ)|=(265598727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395175719/10000000000 : ℝ)|^4115 ≤ (43976760570271/100000000000000 : ℝ)^3091
        have hw : |(5395175719/10000000000 : ℝ)|=(5395175719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076644983/5000000000 : ℝ)|^4115 ≤ (12947019478069/100000000000000 : ℝ)^3091
        have hw : |(-1076644983/5000000000 : ℝ)|=(1076644983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s6_7 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2189828649/5000000000 : ℝ)*x 0 + (4509748019/10000000000 : ℝ)*x 1 + (531676681/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189828649/5000000000 : ℝ)^4115 ≤ (6663230578717/20000000000000 : ℝ)^3091 := by
    have hnat : (2189828649 : ℕ)^4115*20000000000000^3091 ≤ 6663230578717^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189828649 5000000000 6663230578717 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509748019/10000000000 : ℝ)^4115 ≤ (3464003561611/10000000000000 : ℝ)^3091 := by
    have hnat : (4509748019 : ℕ)^4115*10000000000000^3091 ≤ 3464003561611^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509748019 10000000000 3464003561611 10000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531676681/1250000000 : ℝ)^4115 ≤ (640876229587/2000000000000 : ℝ)^3091 := by
    have hnat : (531676681 : ℕ)^4115*2000000000000^3091 ≤ 640876229587^3091*1250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531676681 1250000000 640876229587 2000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189828649/5000000000 : ℝ), (4509748019/10000000000 : ℝ), (531676681/1250000000 : ℝ)] ![(6663230578717/20000000000000 : ℝ), (3464003561611/10000000000000 : ℝ), (640876229587/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189828649/5000000000 : ℝ)|^4115 ≤ (6663230578717/20000000000000 : ℝ)^3091
        have hw : |(2189828649/5000000000 : ℝ)|=(2189828649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509748019/10000000000 : ℝ)|^4115 ≤ (3464003561611/10000000000000 : ℝ)^3091
        have hw : |(4509748019/10000000000 : ℝ)|=(4509748019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531676681/1250000000 : ℝ)|^4115 ≤ (640876229587/2000000000000 : ℝ)^3091
        have hw : |(531676681/1250000000 : ℝ)|=(531676681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1037_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5599/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6999/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (11151/100000 : ℝ) ^ (8229/2048 : ℝ) ≤ (7430424949306199/50000000000000000000 : ℝ) := by
    have hpowers : (11151/100000 : ℝ)^8229 ≤ (7430424949306199/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11151 : ℕ)^8229*50000000000000000000^2048 ≤ 7430424949306199^2048*100000^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11151 100000 7430424949306199 50000000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11151/100000 : ℝ)) (X := (7430424949306199/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14047/100000 : ℝ) ^ (8229/2048 : ℝ) ≤ (7515609800131871/20000000000000000000 : ℝ) := by
    have hpowers : (14047/100000 : ℝ)^8229 ≤ (7515609800131871/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14047 : ℕ)^8229*20000000000000000000^2048 ≤ 7515609800131871^2048*100000^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14047 100000 7515609800131871 20000000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14047/100000 : ℝ)) (X := (7515609800131871/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007430424949306199/25000000000000000000 : ℝ) ≤ (10000739619004023/10000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (25007430424949306199/25000000000000000000 : ℝ)^2048 ≤ (10000739619004023/10000000000000000 : ℝ)^8229 := by
      have hnat : (25007430424949306199 : ℕ)^2048*10000000000000000^8229 ≤ 10000739619004023^8229*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007430424949306199 25000000000000000000 10000739619004023 10000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000739619004023/10000000000000000 : ℝ)) (X := (25007430424949306199/25000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052438898899271753/100000000000000000000 : ℝ) ≤ (5000652410505581/5000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (100052438898899271753/100000000000000000000 : ℝ)^2048 ≤ (5000652410505581/5000000000000000 : ℝ)^8229 := by
      have hnat : (100052438898899271753 : ℕ)^2048*5000000000000000^8229 ≤ 5000652410505581^8229*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052438898899271753 100000000000000000000 5000652410505581 5000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000652410505581/5000000000000000 : ℝ)) (X := (100052438898899271753/100000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007515609800131871/10000000000000000000 : ℝ) ≤ (10001870023018301/10000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (10007515609800131871/10000000000000000000 : ℝ)^2048 ≤ (10001870023018301/10000000000000000 : ℝ)^8229 := by
      have hnat : (10007515609800131871 : ℕ)^2048*10000000000000000^8229 ≤ 10001870023018301^8229*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007515609800131871 10000000000000000000 10001870023018301 10000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001870023018301/10000000000000000 : ℝ)) (X := (10007515609800131871/10000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7430424949306199/50000000000000000000 : ℝ) ≤ ((2894953680147243663/2896000000000000000 : ℝ)+2*(565202007139/289600000000000 : ℝ)*(11151/100000 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (2894953680147243663/2896000000000000000 : ℝ)+2*(565202007139/289600000000000 : ℝ)*(11151/100000 : ℝ)=(10000739619004023/10000000000000000 : ℝ) by norm_num, show 1+2*(7430424949306199/50000000000000000000 : ℝ)=(25007430424949306199/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7515609800131871/20000000000000000000 : ℝ)+(7430424949306199/50000000000000000000 : ℝ) ≤ ((2894953680147243663/2896000000000000000 : ℝ)+(565202007139/289600000000000 : ℝ)*((14047/100000 : ℝ)+(11151/100000 : ℝ)))^(8229/2048 : ℝ) := by
    rw [show (2894953680147243663/2896000000000000000 : ℝ)+(565202007139/289600000000000 : ℝ)*((14047/100000 : ℝ)+(11151/100000 : ℝ))=(5000652410505581/5000000000000000 : ℝ) by norm_num, show 1+(7515609800131871/20000000000000000000 : ℝ)+(7430424949306199/50000000000000000000 : ℝ)=(100052438898899271753/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7515609800131871/20000000000000000000 : ℝ) ≤ ((2894953680147243663/2896000000000000000 : ℝ)+2*(565202007139/289600000000000 : ℝ)*(14047/100000 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (2894953680147243663/2896000000000000000 : ℝ)+2*(565202007139/289600000000000 : ℝ)*(14047/100000 : ℝ)=(10001870023018301/10000000000000000 : ℝ) by norm_num, show 1+2*(7515609800131871/20000000000000000000 : ℝ)=(10007515609800131871/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2894953680147243663/2896000000000000000 : ℝ)*(X 1 0+X 2 0)+(565202007139/289600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (2894953680147243663/2896000000000000000 : ℝ)) (alpha := (565202007139/289600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2894953680147243663/2896000000000000000 : ℝ)*(X 0 1+X 2 1)+(565202007139/289600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (2894953680147243663/2896000000000000000 : ℝ)) (alpha := (565202007139/289600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2894953680147243663/2896000000000000000 : ℝ)*(X 0 2+X 1 2)+(565202007139/289600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (2894953680147243663/2896000000000000000 : ℝ)) (alpha := (565202007139/289600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-110903569/500000000 : ℝ)*X 0 0+(5395511467/10000000000 : ℝ)*X 0 1+(42106341/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668149989/1250000000 : ℝ)*X 1 0+(-1142586571/5000000000 : ℝ)*X 1 1+(5263292551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534519981/1000000000 : ℝ)*X 2 0+(5263292631/10000000000 : ℝ)*X 2 1+(-571293293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218982301/500000000 : ℝ)*X 0 0+(4252760889/10000000000 : ℝ)*X 0 1+(2255199593/5000000000 : ℝ)*X 0 2+(218982301/500000000 : ℝ)*X 1 0+(4252760889/10000000000 : ℝ)*X 1 1+(2255199593/5000000000 : ℝ)*X 1 2+(218982301/500000000 : ℝ)*X 2 0+(4252760889/10000000000 : ℝ)*X 2 1+(2255199593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1109038719/5000000000 : ℝ)*X 0 0+(5263626587/10000000000 : ℝ)*X 0 1+(5395175719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265598727/500000000 : ℝ)*X 1 0+(-1076644983/5000000000 : ℝ)*X 1 1+(5395175719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265598727/500000000 : ℝ)*X 2 0+(5395175719/10000000000 : ℝ)*X 2 1+(-1076644983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189828649/5000000000 : ℝ)*X 0 0+(4509748019/10000000000 : ℝ)*X 0 1+(531676681/1250000000 : ℝ)*X 0 2+(2189828649/5000000000 : ℝ)*X 1 0+(4509748019/10000000000 : ℝ)*X 1 1+(531676681/1250000000 : ℝ)*X 1 2+(2189828649/5000000000 : ℝ)*X 2 0+(4509748019/10000000000 : ℝ)*X 2 1+(531676681/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145478839972827554314424271/28960000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19430147/6250000000000 : ℝ)*(base8) + (2589571/1562500000000 : ℝ)*(base21) + (15296303/25000000000000 : ℝ)*(base29) + (16256011/10000000000000 : ℝ)*(lower3) + (877747/500000000000 : ℝ)*(lower5) + (5722331824977627/100000000000000 : ℝ)*(major0) + (5722331886162839/100000000000000 : ℝ)*(major1) + (5722331886162839/100000000000000 : ℝ)*(major2) + (7563235487781139/100000000000000 : ℝ)*(sp0) + (3781626896975603/50000000000000 : ℝ)*(sp1) + (3781626814109331/50000000000000 : ℝ)*(sp2) + (1940704797429313/50000000000000 : ℝ)*(sp3) + (9028236463/50000000000000 : ℝ)*(sp4) + (38720647/25000000000000 : ℝ)*(sp7) + (1940704874870607/50000000000000 : ℝ)*(f.failure) + (3781626927568209/50000000000000 : ℝ)*(f.sum) + (835539969642341/14480000000000000000000000000 : ℝ)*base65 + (1651334204279449257/289600000000000000000000000000000 : ℝ)*base67 + (17597918019306649257/289600000000000000000000000000000 : ℝ)*base69 + (435047252975137701/289600000000000000000000000000000 : ℝ)*base71 + (1147920714150933/14480000000000000000000000000 : ℝ)*base74 + (2034090097426769257/289600000000000000000000000000000 : ℝ)*base75 + (3239139696194337701/289600000000000000000000000000000 : ℝ)*base77 + (3749401600463569257/289600000000000000000000000000000 : ℝ)*base79 + (48390943328693/14480000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4143551/2500000000000000000000 : ℝ)*base90 + (4143551/2500000000000000000000 : ℝ)*base92 + (4143551/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (552270214889215471200816537/144800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (356963877/50000000000000 : ℝ)*(base19) + (388458939/50000000000000 : ℝ)*(base23) + (76508843/100000000000000 : ℝ)*(upper3) + (28632147/100000000000000 : ℝ)*(lower4) + (77726591/100000000000000 : ℝ)*(upper5) + (5751436623288289/100000000000000 : ℝ)*(major0) + (5751436623288289/100000000000000 : ℝ)*(major1) + (5751436623288289/100000000000000 : ℝ)*(major2) + (19126196759/100000000000000 : ℝ)*(sp1) + (10289690081/50000000000000 : ℝ)*(sp2) + (7601721870485673/100000000000000 : ℝ)*(sp4) + (190042550759029/2500000000000 : ℝ)*(sp5) + (7601700514187633/100000000000000 : ℝ)*(sp6) + (60955488264951/1562500000000 : ℝ)*(sp7) + (60955488264951/1562500000000 : ℝ)*(f.failure) + (7601721870485673/100000000000000 : ℝ)*(f.sum) + (19113366428131/14480000000000000000000000000 : ℝ)*base65 + (2949017930485872607/289600000000000000000000000000000 : ℝ)*base67 + (5475853084002672607/289600000000000000000000000000000 : ℝ)*base69 + (1255609554561072607/289600000000000000000000000000000 : ℝ)*base71 + (22311558834269/14480000000000000000000000000 : ℝ)*base74 + (3700390095967472607/289600000000000000000000000000000 : ℝ)*base75 + (2676769011853872607/289600000000000000000000000000000 : ℝ)*base77 + (2726465746585072607/289600000000000000000000000000000 : ℝ)*base79 + (120232201564771/14480000000000000000000000000 : ℝ)*base81 + (941993/78125000000000000000 : ℝ)*base90 + (941993/78125000000000000000 : ℝ)*base92 + (941993/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1037_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1037_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1037_s7_0 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218118247/10000000000 : ℝ)*x 0 + (5394977127/10000000000 : ℝ)*x 1 + (2631898079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218118247/10000000000 : ℝ)^4115 ≤ (13468512802453/100000000000000 : ℝ)^3091 := by
    have hnat : (2218118247 : ℕ)^4115*100000000000000^3091 ≤ 13468512802453^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218118247 10000000000 13468512802453 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394977127/10000000000 : ℝ)^4115 ≤ (43974605568769/100000000000000 : ℝ)^3091 := by
    have hnat : (5394977127 : ℕ)^4115*100000000000000^3091 ≤ 43974605568769^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394977127 10000000000 43974605568769 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631898079/5000000000 : ℝ)^4115 ≤ (21278440807759/50000000000000 : ℝ)^3091 := by
    have hnat : (2631898079 : ℕ)^4115*50000000000000^3091 ≤ 21278440807759^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631898079 5000000000 21278440807759 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218118247/10000000000 : ℝ), (5394977127/10000000000 : ℝ), (2631898079/5000000000 : ℝ)] ![(13468512802453/100000000000000 : ℝ), (43974605568769/100000000000000 : ℝ), (21278440807759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218118247/10000000000 : ℝ)|^4115 ≤ (13468512802453/100000000000000 : ℝ)^3091
        have hw : |(-2218118247/10000000000 : ℝ)|=(2218118247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394977127/10000000000 : ℝ)|^4115 ≤ (43974605568769/100000000000000 : ℝ)^3091
        have hw : |(5394977127/10000000000 : ℝ)|=(5394977127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631898079/5000000000 : ℝ)|^4115 ≤ (21278440807759/50000000000000 : ℝ)^3091
        have hw : |(2631898079/5000000000 : ℝ)|=(2631898079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s7_1 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345067211/10000000000 : ℝ)*x 0 + (-1142342621/5000000000 : ℝ)*x 1 + (5263795989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345067211/10000000000 : ℝ)^4115 ≤ (8686769596373/20000000000000 : ℝ)^3091 := by
    have hnat : (5345067211 : ℕ)^4115*20000000000000^3091 ≤ 8686769596373^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345067211 10000000000 8686769596373 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142342621/5000000000 : ℝ)^4115 ≤ (7004636102129/50000000000000 : ℝ)^3091 := by
    have hnat : (1142342621 : ℕ)^4115*50000000000000^3091 ≤ 7004636102129^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142342621 5000000000 7004636102129 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263795989/10000000000 : ℝ)^4115 ≤ (42556879796537/100000000000000 : ℝ)^3091 := by
    have hnat : (5263795989 : ℕ)^4115*100000000000000^3091 ≤ 42556879796537^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263795989 10000000000 42556879796537 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345067211/10000000000 : ℝ), (-1142342621/5000000000 : ℝ), (5263795989/10000000000 : ℝ)] ![(8686769596373/20000000000000 : ℝ), (7004636102129/50000000000000 : ℝ), (42556879796537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345067211/10000000000 : ℝ)|^4115 ≤ (8686769596373/20000000000000 : ℝ)^3091
        have hw : |(5345067211/10000000000 : ℝ)|=(5345067211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1142342621/5000000000 : ℝ)|^4115 ≤ (7004636102129/50000000000000 : ℝ)^3091
        have hw : |(-1142342621/5000000000 : ℝ)|=(1142342621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263795989/10000000000 : ℝ)|^4115 ≤ (42556879796537/100000000000000 : ℝ)^3091
        have hw : |(5263795989/10000000000 : ℝ)|=(5263795989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s7_2 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133626679/250000000 : ℝ)*x 0 + (328987257/625000000 : ℝ)*x 1 + (-2284685147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133626679/250000000 : ℝ)^4115 ≤ (10858461857537/25000000000000 : ℝ)^3091 := by
    have hnat : (133626679 : ℕ)^4115*25000000000000^3091 ≤ 10858461857537^3091*250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133626679 250000000 10858461857537 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328987257/625000000 : ℝ)^4115 ≤ (42556881120411/100000000000000 : ℝ)^3091 := by
    have hnat : (328987257 : ℕ)^4115*100000000000000^3091 ≤ 42556881120411^3091*625000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328987257 625000000 42556881120411 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284685147/10000000000 : ℝ)^4115 ≤ (2801854285751/20000000000000 : ℝ)^3091 := by
    have hnat : (2284685147 : ℕ)^4115*20000000000000^3091 ≤ 2801854285751^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284685147 10000000000 2801854285751 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133626679/250000000 : ℝ), (328987257/625000000 : ℝ), (-2284685147/10000000000 : ℝ)] ![(10858461857537/25000000000000 : ℝ), (42556881120411/100000000000000 : ℝ), (2801854285751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133626679/250000000 : ℝ)|^4115 ≤ (10858461857537/25000000000000 : ℝ)^3091
        have hw : |(133626679/250000000 : ℝ)|=(133626679/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328987257/625000000 : ℝ)|^4115 ≤ (42556881120411/100000000000000 : ℝ)^3091
        have hw : |(328987257/625000000 : ℝ)|=(328987257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2284685147/10000000000 : ℝ)|^4115 ≤ (2801854285751/20000000000000 : ℝ)^3091
        have hw : |(-2284685147/10000000000 : ℝ)|=(2284685147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s7_3 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2189836819/5000000000 : ℝ)*x 0 + (4253767271/10000000000 : ℝ)*x 1 + (1127346199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189836819/5000000000 : ℝ)^4115 ≤ (16658159185337/50000000000000 : ℝ)^3091 := by
    have hnat : (2189836819 : ℕ)^4115*50000000000000^3091 ≤ 16658159185337^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189836819 5000000000 16658159185337 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253767271/10000000000 : ℝ)^4115 ≤ (16023680090331/50000000000000 : ℝ)^3091 := by
    have hnat : (4253767271 : ℕ)^4115*50000000000000^3091 ≤ 16023680090331^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253767271 10000000000 16023680090331 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127346199/2500000000 : ℝ)^4115 ≤ (17318160711693/50000000000000 : ℝ)^3091 := by
    have hnat : (1127346199 : ℕ)^4115*50000000000000^3091 ≤ 17318160711693^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127346199 2500000000 17318160711693 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189836819/5000000000 : ℝ), (4253767271/10000000000 : ℝ), (1127346199/2500000000 : ℝ)] ![(16658159185337/50000000000000 : ℝ), (16023680090331/50000000000000 : ℝ), (17318160711693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189836819/5000000000 : ℝ)|^4115 ≤ (16658159185337/50000000000000 : ℝ)^3091
        have hw : |(2189836819/5000000000 : ℝ)|=(2189836819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253767271/10000000000 : ℝ)|^4115 ≤ (16023680090331/50000000000000 : ℝ)^3091
        have hw : |(4253767271/10000000000 : ℝ)|=(4253767271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127346199/2500000000 : ℝ)|^4115 ≤ (17318160711693/50000000000000 : ℝ)^3091
        have hw : |(1127346199/2500000000 : ℝ)|=(1127346199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s7_4 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-443624693/2000000000 : ℝ)*x 0 + (5264124973/10000000000 : ℝ)*x 1 + (5394647089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443624693/2000000000 : ℝ)^4115 ≤ (3367138745697/25000000000000 : ℝ)^3091 := by
    have hnat : (443624693 : ℕ)^4115*25000000000000^3091 ≤ 3367138745697^3091*2000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443624693 2000000000 3367138745697 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264124973/10000000000 : ℝ)^4115 ≤ (21280210377519/50000000000000 : ℝ)^3091 := by
    have hnat : (5264124973 : ℕ)^4115*50000000000000^3091 ≤ 21280210377519^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264124973 10000000000 21280210377519 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394647089/10000000000 : ℝ)^4115 ≤ (43971024252091/100000000000000 : ℝ)^3091 := by
    have hnat : (5394647089 : ℕ)^4115*100000000000000^3091 ≤ 43971024252091^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394647089 10000000000 43971024252091 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443624693/2000000000 : ℝ), (5264124973/10000000000 : ℝ), (5394647089/10000000000 : ℝ)] ![(3367138745697/25000000000000 : ℝ), (21280210377519/50000000000000 : ℝ), (43971024252091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443624693/2000000000 : ℝ)|^4115 ≤ (3367138745697/25000000000000 : ℝ)^3091
        have hw : |(-443624693/2000000000 : ℝ)|=(443624693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264124973/10000000000 : ℝ)|^4115 ≤ (21280210377519/50000000000000 : ℝ)^3091
        have hw : |(5264124973/10000000000 : ℝ)|=(5264124973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394647089/10000000000 : ℝ)|^4115 ≤ (43971024252091/100000000000000 : ℝ)^3091
        have hw : |(5394647089/10000000000 : ℝ)|=(5394647089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s7_5 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656051277/5000000000 : ℝ)*x 0 + (-1076917121/5000000000 : ℝ)*x 1 + (5394646851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656051277/5000000000 : ℝ)^4115 ≤ (215388009761/500000000000 : ℝ)^3091 := by
    have hnat : (2656051277 : ℕ)^4115*500000000000^3091 ≤ 215388009761^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656051277 5000000000 215388009761 500000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076917121/5000000000 : ℝ)^4115 ≤ (2590275271387/20000000000000 : ℝ)^3091 := by
    have hnat : (1076917121 : ℕ)^4115*20000000000000^3091 ≤ 2590275271387^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076917121 5000000000 2590275271387 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394646851/10000000000 : ℝ)^4115 ≤ (1758840866781/4000000000000 : ℝ)^3091 := by
    have hnat : (5394646851 : ℕ)^4115*4000000000000^3091 ≤ 1758840866781^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394646851 10000000000 1758840866781 4000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656051277/5000000000 : ℝ), (-1076917121/5000000000 : ℝ), (5394646851/10000000000 : ℝ)] ![(215388009761/500000000000 : ℝ), (2590275271387/20000000000000 : ℝ), (1758840866781/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656051277/5000000000 : ℝ)|^4115 ≤ (215388009761/500000000000 : ℝ)^3091
        have hw : |(2656051277/5000000000 : ℝ)|=(2656051277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076917121/5000000000 : ℝ)|^4115 ≤ (2590275271387/20000000000000 : ℝ)^3091
        have hw : |(-1076917121/5000000000 : ℝ)|=(1076917121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394646851/10000000000 : ℝ)|^4115 ≤ (1758840866781/4000000000000 : ℝ)^3091
        have hw : |(5394646851/10000000000 : ℝ)|=(5394646851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s7_6 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062420491/2000000000 : ℝ)*x 0 + (168582723/312500000 : ℝ)*x 1 + (-2153833991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062420491/2000000000 : ℝ)^4115 ≤ (43077600883413/100000000000000 : ℝ)^3091 := by
    have hnat : (1062420491 : ℕ)^4115*100000000000000^3091 ≤ 43077600883413^3091*2000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062420491 2000000000 43077600883413 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168582723/312500000 : ℝ)^4115 ≤ (43971024762093/100000000000000 : ℝ)^3091 := by
    have hnat : (168582723 : ℕ)^4115*100000000000000^3091 ≤ 43971024762093^3091*312500000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168582723 312500000 43971024762093 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153833991/10000000000 : ℝ)^4115 ≤ (647568717381/5000000000000 : ℝ)^3091 := by
    have hnat : (2153833991 : ℕ)^4115*5000000000000^3091 ≤ 647568717381^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153833991 10000000000 647568717381 5000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062420491/2000000000 : ℝ), (168582723/312500000 : ℝ), (-2153833991/10000000000 : ℝ)] ![(43077600883413/100000000000000 : ℝ), (43971024762093/100000000000000 : ℝ), (647568717381/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062420491/2000000000 : ℝ)|^4115 ≤ (43077600883413/100000000000000 : ℝ)^3091
        have hw : |(1062420491/2000000000 : ℝ)|=(1062420491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168582723/312500000 : ℝ)|^4115 ≤ (43971024762093/100000000000000 : ℝ)^3091
        have hw : |(168582723/312500000 : ℝ)|=(168582723/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153833991/10000000000 : ℝ)|^4115 ≤ (647568717381/5000000000000 : ℝ)^3091
        have hw : |(-2153833991/10000000000 : ℝ)|=(2153833991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s7_7 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (437968313/1000000000 : ℝ)*x 0 + (2254372293/5000000000 : ℝ)*x 1 + (1063602591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437968313/1000000000 : ℝ)^4115 ≤ (33316414497361/100000000000000 : ℝ)^3091 := by
    have hnat : (437968313 : ℕ)^4115*100000000000000^3091 ≤ 33316414497361^3091*1000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437968313 1000000000 33316414497361 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254372293/5000000000 : ℝ)^4115 ≤ (2164360943671/6250000000000 : ℝ)^3091 := by
    have hnat : (2254372293 : ℕ)^4115*6250000000000^3091 ≤ 2164360943671^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254372293 5000000000 2164360943671 6250000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063602591/2500000000 : ℝ)^4115 ≤ (32053810393243/100000000000000 : ℝ)^3091 := by
    have hnat : (1063602591 : ℕ)^4115*100000000000000^3091 ≤ 32053810393243^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063602591 2500000000 32053810393243 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437968313/1000000000 : ℝ), (2254372293/5000000000 : ℝ), (1063602591/2500000000 : ℝ)] ![(33316414497361/100000000000000 : ℝ), (2164360943671/6250000000000 : ℝ), (32053810393243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437968313/1000000000 : ℝ)|^4115 ≤ (33316414497361/100000000000000 : ℝ)^3091
        have hw : |(437968313/1000000000 : ℝ)|=(437968313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254372293/5000000000 : ℝ)|^4115 ≤ (2164360943671/6250000000000 : ℝ)^3091
        have hw : |(2254372293/5000000000 : ℝ)|=(2254372293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063602591/2500000000 : ℝ)|^4115 ≤ (32053810393243/100000000000000 : ℝ)^3091
        have hw : |(1063602591/2500000000 : ℝ)|=(1063602591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1037_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1401/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5599/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5599/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5599/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5599/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5599/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5599/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5599/50000 : ℝ) ^ (8229/2048 : ℝ) ≤ (15114132944045021/100000000000000000000 : ℝ) := by
    have hpowers : (5599/50000 : ℝ)^8229 ≤ (15114132944045021/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5599 : ℕ)^8229*100000000000000000000^2048 ≤ 15114132944045021^2048*50000^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5599 50000 15114132944045021 100000000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5599/50000 : ℝ)) (X := (15114132944045021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6999/50000 : ℝ) ^ (8229/2048 : ℝ) ≤ (37054114395631161/100000000000000000000 : ℝ) := by
    have hpowers : (6999/50000 : ℝ)^8229 ≤ (37054114395631161/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6999 : ℕ)^8229*100000000000000000000^2048 ≤ 37054114395631161^2048*50000^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6999 50000 37054114395631161 100000000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6999/50000 : ℝ)) (X := (37054114395631161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015114132944045021/50000000000000000000 : ℝ) ≤ (2500188055844197/2500000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (50015114132944045021/50000000000000000000 : ℝ)^2048 ≤ (2500188055844197/2500000000000000 : ℝ)^8229 := by
      have hnat : (50015114132944045021 : ℕ)^2048*2500000000000000^8229 ≤ 2500188055844197^8229*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015114132944045021 50000000000000000000 2500188055844197 2500000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500188055844197/2500000000000000 : ℝ)) (X := (50015114132944045021/50000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026084123669838091/50000000000000000000 : ℝ) ≤ (10001298087790467/10000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (50026084123669838091/50000000000000000000 : ℝ)^2048 ≤ (10001298087790467/10000000000000000 : ℝ)^8229 := by
      have hnat : (50026084123669838091 : ℕ)^2048*10000000000000000^8229 ≤ 10001298087790467^8229*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026084123669838091 50000000000000000000 10001298087790467 10000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001298087790467/10000000000000000 : ℝ)) (X := (50026084123669838091/50000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037054114395631161/50000000000000000000 : ℝ) ≤ (5000921976102073/5000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (50037054114395631161/50000000000000000000 : ℝ)^2048 ≤ (5000921976102073/5000000000000000 : ℝ)^8229 := by
      have hnat : (50037054114395631161 : ℕ)^2048*5000000000000000^8229 ≤ 5000921976102073^8229*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037054114395631161 50000000000000000000 5000921976102073 5000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000921976102073/5000000000000000 : ℝ)) (X := (50037054114395631161/50000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15114132944045021/100000000000000000000 : ℝ) ≤ ((6997470261511562879/7000000000000000000 : ℝ)+2*(545864413679/280000000000000 : ℝ)*(5599/50000 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (6997470261511562879/7000000000000000000 : ℝ)+2*(545864413679/280000000000000 : ℝ)*(5599/50000 : ℝ)=(2500188055844197/2500000000000000 : ℝ) by norm_num, show 1+2*(15114132944045021/100000000000000000000 : ℝ)=(50015114132944045021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37054114395631161/100000000000000000000 : ℝ)+(15114132944045021/100000000000000000000 : ℝ) ≤ ((6997470261511562879/7000000000000000000 : ℝ)+(545864413679/280000000000000 : ℝ)*((6999/50000 : ℝ)+(5599/50000 : ℝ)))^(8229/2048 : ℝ) := by
    rw [show (6997470261511562879/7000000000000000000 : ℝ)+(545864413679/280000000000000 : ℝ)*((6999/50000 : ℝ)+(5599/50000 : ℝ))=(10001298087790467/10000000000000000 : ℝ) by norm_num, show 1+(37054114395631161/100000000000000000000 : ℝ)+(15114132944045021/100000000000000000000 : ℝ)=(50026084123669838091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37054114395631161/100000000000000000000 : ℝ) ≤ ((6997470261511562879/7000000000000000000 : ℝ)+2*(545864413679/280000000000000 : ℝ)*(6999/50000 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (6997470261511562879/7000000000000000000 : ℝ)+2*(545864413679/280000000000000 : ℝ)*(6999/50000 : ℝ)=(5000921976102073/5000000000000000 : ℝ) by norm_num, show 1+2*(37054114395631161/100000000000000000000 : ℝ)=(50037054114395631161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6997470261511562879/7000000000000000000 : ℝ)*(X 1 0+X 2 0)+(545864413679/280000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (6997470261511562879/7000000000000000000 : ℝ)) (alpha := (545864413679/280000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6997470261511562879/7000000000000000000 : ℝ)*(X 0 1+X 2 1)+(545864413679/280000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (6997470261511562879/7000000000000000000 : ℝ)) (alpha := (545864413679/280000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6997470261511562879/7000000000000000000 : ℝ)*(X 0 2+X 1 2)+(545864413679/280000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (6997470261511562879/7000000000000000000 : ℝ)) (alpha := (545864413679/280000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2218118247/10000000000 : ℝ)*X 0 0+(5394977127/10000000000 : ℝ)*X 0 1+(2631898079/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345067211/10000000000 : ℝ)*X 1 0+(-1142342621/5000000000 : ℝ)*X 1 1+(5263795989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133626679/250000000 : ℝ)*X 2 0+(328987257/625000000 : ℝ)*X 2 1+(-2284685147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2189836819/5000000000 : ℝ)*X 0 0+(4253767271/10000000000 : ℝ)*X 0 1+(1127346199/2500000000 : ℝ)*X 0 2+(2189836819/5000000000 : ℝ)*X 1 0+(4253767271/10000000000 : ℝ)*X 1 1+(1127346199/2500000000 : ℝ)*X 1 2+(2189836819/5000000000 : ℝ)*X 2 0+(4253767271/10000000000 : ℝ)*X 2 1+(1127346199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-443624693/2000000000 : ℝ)*X 0 0+(5264124973/10000000000 : ℝ)*X 0 1+(5394647089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656051277/5000000000 : ℝ)*X 1 0+(-1076917121/5000000000 : ℝ)*X 1 1+(5394646851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062420491/2000000000 : ℝ)*X 2 0+(168582723/312500000 : ℝ)*X 2 1+(-2153833991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437968313/1000000000 : ℝ)*X 0 0+(2254372293/5000000000 : ℝ)*X 0 1+(1063602591/2500000000 : ℝ)*X 0 2+(437968313/1000000000 : ℝ)*X 1 0+(2254372293/5000000000 : ℝ)*X 1 1+(1063602591/2500000000 : ℝ)*X 1 2+(437968313/1000000000 : ℝ)*X 2 0+(2254372293/5000000000 : ℝ)*X 2 1+(1063602591/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (769940679979634708715850167/70000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65997861/3125000000000 : ℝ)*(base19) + (87933663/5000000000000 : ℝ)*(base23) + (74970423/50000000000000 : ℝ)*(lower2) + (111318703/50000000000000 : ℝ)*(upper3) + (147007077/100000000000000 : ℝ)*(upper5) + (1153530765146691/20000000000000 : ℝ)*(major0) + (1153530765146691/20000000000000 : ℝ)*(major1) + (1153530765146691/20000000000000 : ℝ)*(major2) + (304924258455773/4000000000000 : ℝ)*(sp0) + (7623153931465599/100000000000000 : ℝ)*(sp1) + (7623154284723891/100000000000000 : ℝ)*(sp2) + (61126900751309/1562500000000 : ℝ)*(sp3) + (49582002827/100000000000000 : ℝ)*(sp4) + (7398336889/25000000000000 : ℝ)*(sp7) + (978037810357833/25000000000000 : ℝ)*(f.failure) + (7623156043397151/100000000000000 : ℝ)*(f.sum) + (19471180079789/2800000000000000000000000000 : ℝ)*base65 + (932169793359991611/140000000000000000000000000000000 : ℝ)*base68 + (493067450140008389/140000000000000000000000000000000 : ℝ)*base69 + (700311831219991611/140000000000000000000000000000000 : ℝ)*base72 + (5786477954989/2800000000000000000000000000 : ℝ)*base73 + (2332742733979991611/140000000000000000000000000000000 : ℝ)*base76 + (1390987844840008389/140000000000000000000000000000000 : ℝ)*base77 + (1431887031799991611/140000000000000000000000000000000 : ℝ)*base80 + (20771958702211/2800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1466631/1250000000000000000000 : ℝ)*base89 + (1466631/1250000000000000000000 : ℝ)*base91 + (1466631/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83271696769909542788920983/14000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (430723613/50000000000000 : ℝ)*(base19) + (1149473279/100000000000000 : ℝ)*(base23) + (38187069/25000000000000 : ℝ)*(upper2) + (5690907/25000000000000 : ℝ)*(lower5) + (231867532827741/4000000000000 : ℝ)*(major0) + (231867532827741/4000000000000 : ℝ)*(major1) + (231867532827741/4000000000000 : ℝ)*(major2) + (16383722707/100000000000000 : ℝ)*(sp1) + (19734993287/50000000000000 : ℝ)*(sp2) + (738632497/12500000000000 : ℝ)*(sp3) + (3830765673573037/50000000000000 : ℝ)*(sp4) + (383075705098807/5000000000000 : ℝ)*(sp5) + (7661490727686221/100000000000000 : ℝ)*(sp6) + (3931839186915049/100000000000000 : ℝ)*(sp7) + (157273803839001/4000000000000 : ℝ)*(f.failure) + (3830765673573037/50000000000000 : ℝ)*(f.sum) + (1755854333741/560000000000000000000000000 : ℝ)*base66 + (70972429989501339/28000000000000000000000000000000 : ℝ)*base67 + (124369967021501339/28000000000000000000000000000000 : ℝ)*base69 + (11807654334498661/28000000000000000000000000000000 : ℝ)*base72 + (652001703021/560000000000000000000000000 : ℝ)*base74 + (405459761265501339/28000000000000000000000000000000 : ℝ)*base75 + (245024152758498661/28000000000000000000000000000000 : ℝ)*base78 + (448541024413501339/28000000000000000000000000000000 : ℝ)*base79 + (1029681597059/560000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (12393/200000000000000000000 : ℝ)*base90 + (12393/200000000000000000000 : ℝ)*base92 + (12393/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1037_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1037_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1037_s8_0 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-443626051/2000000000 : ℝ)*x 0 + (134871533/250000000 : ℝ)*x 1 + (2631951947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443626051/2000000000 : ℝ)^4115 ≤ (21549775793/160000000000 : ℝ)^3091 := by
    have hnat : (443626051 : ℕ)^4115*160000000000^3091 ≤ 21549775793^3091*2000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443626051 2000000000 21549775793 160000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134871533/250000000 : ℝ)^4115 ≤ (43973348912661/100000000000000 : ℝ)^3091 := by
    have hnat : (134871533 : ℕ)^4115*100000000000000^3091 ≤ 43973348912661^3091*250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134871533 250000000 43973348912661 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631951947/5000000000 : ℝ)^4115 ≤ (10639510300997/25000000000000 : ℝ)^3091 := by
    have hnat : (2631951947 : ℕ)^4115*25000000000000^3091 ≤ 10639510300997^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631951947 5000000000 10639510300997 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443626051/2000000000 : ℝ), (134871533/250000000 : ℝ), (2631951947/5000000000 : ℝ)] ![(21549775793/160000000000 : ℝ), (43973348912661/100000000000000 : ℝ), (10639510300997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443626051/2000000000 : ℝ)|^4115 ≤ (21549775793/160000000000 : ℝ)^3091
        have hw : |(-443626051/2000000000 : ℝ)|=(443626051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134871533/250000000 : ℝ)|^4115 ≤ (43973348912661/100000000000000 : ℝ)^3091
        have hw : |(134871533/250000000 : ℝ)|=(134871533/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631951947/5000000000 : ℝ)|^4115 ≤ (10639510300997/25000000000000 : ℝ)^3091
        have hw : |(2631951947/5000000000 : ℝ)|=(2631951947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s8_1 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345037871/10000000000 : ℝ)*x 0 + (-2284581943/10000000000 : ℝ)*x 1 + (5263903823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345037871/10000000000 : ℝ)^4115 ≤ (43433530582769/100000000000000 : ℝ)^3091 := by
    have hnat : (5345037871 : ℕ)^4115*100000000000000^3091 ≤ 43433530582769^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345037871 10000000000 43433530582769 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284581943/10000000000 : ℝ)^4115 ≤ (14008428960963/100000000000000 : ℝ)^3091 := by
    have hnat : (2284581943 : ℕ)^4115*100000000000000^3091 ≤ 14008428960963^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284581943 10000000000 14008428960963 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263903823/10000000000 : ℝ)^4115 ≤ (10639510109949/25000000000000 : ℝ)^3091 := by
    have hnat : (5263903823 : ℕ)^4115*25000000000000^3091 ≤ 10639510109949^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263903823 10000000000 10639510109949 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345037871/10000000000 : ℝ), (-2284581943/10000000000 : ℝ), (5263903823/10000000000 : ℝ)] ![(43433530582769/100000000000000 : ℝ), (14008428960963/100000000000000 : ℝ), (10639510109949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345037871/10000000000 : ℝ)|^4115 ≤ (43433530582769/100000000000000 : ℝ)^3091
        have hw : |(5345037871/10000000000 : ℝ)|=(5345037871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284581943/10000000000 : ℝ)|^4115 ≤ (14008428960963/100000000000000 : ℝ)^3091
        have hw : |(-2284581943/10000000000 : ℝ)|=(2284581943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263903823/10000000000 : ℝ)|^4115 ≤ (10639510109949/25000000000000 : ℝ)^3091
        have hw : |(5263903823/10000000000 : ℝ)|=(5263903823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s8_2 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345037819/10000000000 : ℝ)*x 0 + (2631951947/5000000000 : ℝ)*x 1 + (-2284581919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345037819/10000000000 : ℝ)^4115 ≤ (8686706004047/20000000000000 : ℝ)^3091 := by
    have hnat : (5345037819 : ℕ)^4115*20000000000000^3091 ≤ 8686706004047^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345037819 10000000000 8686706004047 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631951947/5000000000 : ℝ)^4115 ≤ (10639510300997/25000000000000 : ℝ)^3091 := by
    have hnat : (2631951947 : ℕ)^4115*25000000000000^3091 ≤ 10639510300997^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631951947 5000000000 10639510300997 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284581919/10000000000 : ℝ)^4115 ≤ (14008428765049/100000000000000 : ℝ)^3091 := by
    have hnat : (2284581919 : ℕ)^4115*100000000000000^3091 ≤ 14008428765049^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284581919 10000000000 14008428765049 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345037819/10000000000 : ℝ), (2631951947/5000000000 : ℝ), (-2284581919/10000000000 : ℝ)] ![(8686706004047/20000000000000 : ℝ), (10639510300997/25000000000000 : ℝ), (14008428765049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345037819/10000000000 : ℝ)|^4115 ≤ (8686706004047/20000000000000 : ℝ)^3091
        have hw : |(5345037819/10000000000 : ℝ)|=(5345037819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631951947/5000000000 : ℝ)|^4115 ≤ (10639510300997/25000000000000 : ℝ)^3091
        have hw : |(2631951947/5000000000 : ℝ)|=(2631951947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2284581919/10000000000 : ℝ)|^4115 ≤ (14008428765049/100000000000000 : ℝ)^3091
        have hw : |(-2284581919/10000000000 : ℝ)|=(2284581919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s8_3 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4379679381/10000000000 : ℝ)*x 0 + (4253984447/10000000000 : ℝ)*x 1 + (563645761/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379679381/10000000000 : ℝ)^4115 ≤ (6663275306151/20000000000000 : ℝ)^3091 := by
    have hnat : (4379679381 : ℕ)^4115*20000000000000^3091 ≤ 6663275306151^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379679381 10000000000 6663275306151 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253984447/10000000000 : ℝ)^4115 ≤ (3204953841637/10000000000000 : ℝ)^3091 := by
    have hnat : (4253984447 : ℕ)^4115*10000000000000^3091 ≤ 3204953841637^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253984447 10000000000 3204953841637 10000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563645761/1250000000 : ℝ)^4115 ≤ (6926817007771/20000000000000 : ℝ)^3091 := by
    have hnat : (563645761 : ℕ)^4115*20000000000000^3091 ≤ 6926817007771^3091*1250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563645761 1250000000 6926817007771 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379679381/10000000000 : ℝ), (4253984447/10000000000 : ℝ), (563645761/1250000000 : ℝ)] ![(6663275306151/20000000000000 : ℝ), (3204953841637/10000000000000 : ℝ), (6926817007771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379679381/10000000000 : ℝ)|^4115 ≤ (6663275306151/20000000000000 : ℝ)^3091
        have hw : |(4379679381/10000000000 : ℝ)|=(4379679381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253984447/10000000000 : ℝ)|^4115 ≤ (3204953841637/10000000000000 : ℝ)^3091
        have hw : |(4253984447/10000000000 : ℝ)|=(4253984447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563645761/1250000000 : ℝ)|^4115 ≤ (6926817007771/20000000000000 : ℝ)^3091
        have hw : |(563645761/1250000000 : ℝ)|=(563645761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s8_4 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218135337/10000000000 : ℝ)*x 0 + (658028957/1250000000 : ℝ)*x 1 + (2697266211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218135337/10000000000 : ℝ)^4115 ≤ (13468650951661/100000000000000 : ℝ)^3091 := by
    have hnat : (2218135337 : ℕ)^4115*100000000000000^3091 ≤ 13468650951661^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218135337 10000000000 13468650951661 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658028957/1250000000 : ℝ)^4115 ≤ (2128078451677/5000000000000 : ℝ)^3091 := by
    have hnat : (658028957 : ℕ)^4115*5000000000000^3091 ≤ 2128078451677^3091*1250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658028957 1250000000 2128078451677 5000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697266211/5000000000 : ℝ)^4115 ≤ (8793955998327/20000000000000 : ℝ)^3091 := by
    have hnat : (2697266211 : ℕ)^4115*20000000000000^3091 ≤ 8793955998327^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697266211 5000000000 8793955998327 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218135337/10000000000 : ℝ), (658028957/1250000000 : ℝ), (2697266211/5000000000 : ℝ)] ![(13468650951661/100000000000000 : ℝ), (2128078451677/5000000000000 : ℝ), (8793955998327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218135337/10000000000 : ℝ)|^4115 ≤ (13468650951661/100000000000000 : ℝ)^3091
        have hw : |(-2218135337/10000000000 : ℝ)|=(2218135337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658028957/1250000000 : ℝ)|^4115 ≤ (2128078451677/5000000000000 : ℝ)^3091
        have hw : |(658028957/1250000000 : ℝ)|=(658028957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697266211/5000000000 : ℝ)|^4115 ≤ (8793955998327/20000000000000 : ℝ)^3091
        have hw : |(2697266211/5000000000 : ℝ)|=(2697266211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s8_5 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106242583/200000000 : ℝ)*x 0 + (-538488411/2500000000 : ℝ)*x 1 + (5394532303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106242583/200000000 : ℝ)^4115 ≤ (10769472269561/25000000000000 : ℝ)^3091 := by
    have hnat : (106242583 : ℕ)^4115*25000000000000^3091 ≤ 10769472269561^3091*200000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106242583 200000000 10769472269561 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538488411/2500000000 : ℝ)^4115 ≤ (12952332207653/100000000000000 : ℝ)^3091 := by
    have hnat : (538488411 : ℕ)^4115*100000000000000^3091 ≤ 12952332207653^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538488411 2500000000 12952332207653 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394532303/10000000000 : ℝ)^4115 ≤ (43969778700361/100000000000000 : ℝ)^3091 := by
    have hnat : (5394532303 : ℕ)^4115*100000000000000^3091 ≤ 43969778700361^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394532303 10000000000 43969778700361 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106242583/200000000 : ℝ), (-538488411/2500000000 : ℝ), (5394532303/10000000000 : ℝ)] ![(10769472269561/25000000000000 : ℝ), (12952332207653/100000000000000 : ℝ), (43969778700361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106242583/200000000 : ℝ)|^4115 ≤ (10769472269561/25000000000000 : ℝ)^3091
        have hw : |(106242583/200000000 : ℝ)|=(106242583/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538488411/2500000000 : ℝ)|^4115 ≤ (12952332207653/100000000000000 : ℝ)^3091
        have hw : |(-538488411/2500000000 : ℝ)|=(538488411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394532303/10000000000 : ℝ)|^4115 ≤ (43969778700361/100000000000000 : ℝ)^3091
        have hw : |(5394532303/10000000000 : ℝ)|=(5394532303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s8_6 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312129503/10000000000 : ℝ)*x 0 + (1348633087/2500000000 : ℝ)*x 1 + (-2153953107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312129503/10000000000 : ℝ)^4115 ≤ (43077892889177/100000000000000 : ℝ)^3091 := by
    have hnat : (5312129503 : ℕ)^4115*100000000000000^3091 ≤ 43077892889177^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312129503 10000000000 43077892889177 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348633087/2500000000 : ℝ)^4115 ≤ (21984889594329/50000000000000 : ℝ)^3091 := by
    have hnat : (1348633087 : ℕ)^4115*50000000000000^3091 ≤ 21984889594329^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348633087 2500000000 21984889594329 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153953107/10000000000 : ℝ)^4115 ≤ (12952327908759/100000000000000 : ℝ)^3091 := by
    have hnat : (2153953107 : ℕ)^4115*100000000000000^3091 ≤ 12952327908759^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153953107 10000000000 12952327908759 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312129503/10000000000 : ℝ), (1348633087/2500000000 : ℝ), (-2153953107/10000000000 : ℝ)] ![(43077892889177/100000000000000 : ℝ), (21984889594329/50000000000000 : ℝ), (12952327908759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312129503/10000000000 : ℝ)|^4115 ≤ (43077892889177/100000000000000 : ℝ)^3091
        have hw : |(5312129503/10000000000 : ℝ)|=(5312129503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348633087/2500000000 : ℝ)|^4115 ≤ (21984889594329/50000000000000 : ℝ)^3091
        have hw : |(1348633087/2500000000 : ℝ)|=(1348633087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153953107/10000000000 : ℝ)|^4115 ≤ (12952327908759/100000000000000 : ℝ)^3091
        have hw : |(-2153953107/10000000000 : ℝ)|=(2153953107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s8_7 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875937891/2000000000 : ℝ)*x 0 + (901705533/2000000000 : ℝ)*x 1 + (4254625107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875937891/2000000000 : ℝ)^4115 ≤ (8329119637869/25000000000000 : ℝ)^3091 := by
    have hnat : (875937891 : ℕ)^4115*25000000000000^3091 ≤ 8329119637869^3091*2000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875937891 2000000000 8329119637869 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901705533/2000000000 : ℝ)^4115 ≤ (6925511418249/20000000000000 : ℝ)^3091 := by
    have hnat : (901705533 : ℕ)^4115*20000000000000^3091 ≤ 6925511418249^3091*2000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901705533 2000000000 6925511418249 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254625107/10000000000 : ℝ)^4115 ≤ (6411192866813/20000000000000 : ℝ)^3091 := by
    have hnat : (4254625107 : ℕ)^4115*20000000000000^3091 ≤ 6411192866813^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254625107 10000000000 6411192866813 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875937891/2000000000 : ℝ), (901705533/2000000000 : ℝ), (4254625107/10000000000 : ℝ)] ![(8329119637869/25000000000000 : ℝ), (6925511418249/20000000000000 : ℝ), (6411192866813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875937891/2000000000 : ℝ)|^4115 ≤ (8329119637869/25000000000000 : ℝ)^3091
        have hw : |(875937891/2000000000 : ℝ)|=(875937891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901705533/2000000000 : ℝ)|^4115 ≤ (6925511418249/20000000000000 : ℝ)^3091
        have hw : |(901705533/2000000000 : ℝ)|=(901705533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254625107/10000000000 : ℝ)|^4115 ≤ (6411192866813/20000000000000 : ℝ)^3091
        have hw : |(4254625107/10000000000 : ℝ)|=(4254625107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1037_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11211/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2797/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1401/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1401/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1401/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1401/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1401/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1401/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1401/12500 : ℝ) ^ (8229/2048 : ℝ) ≤ (1516843860372329/10000000000000000000 : ℝ) := by
    have hpowers : (1401/12500 : ℝ)^8229 ≤ (1516843860372329/10000000000000000000 : ℝ)^2048 := by
      have hnat : (1401 : ℕ)^8229*10000000000000000000^2048 ≤ 1516843860372329^2048*12500^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 12500 1516843860372329 10000000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/12500 : ℝ)) (X := (1516843860372329/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13987/100000 : ℝ) ^ (8229/2048 : ℝ) ≤ (18468627288516327/50000000000000000000 : ℝ) := by
    have hpowers : (13987/100000 : ℝ)^8229 ≤ (18468627288516327/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13987 : ℕ)^8229*50000000000000000000^2048 ≤ 18468627288516327^2048*100000^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13987 100000 18468627288516327 50000000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13987/100000 : ℝ)) (X := (18468627288516327/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001516843860372329/5000000000000000000 : ℝ) ≤ (2000150985167277/2000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (5001516843860372329/5000000000000000000 : ℝ)^2048 ≤ (2000150985167277/2000000000000000 : ℝ)^8229 := by
      have hnat : (5001516843860372329 : ℕ)^2048*2000000000000000^8229 ≤ 2000150985167277^8229*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001516843860372329 5000000000000000000 2000150985167277 2000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000150985167277/2000000000000000 : ℝ)) (X := (5001516843860372329/5000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506513211647594493/12500000000000000000 : ℝ) ≤ (2000259306315487/2000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (12506513211647594493/12500000000000000000 : ℝ)^2048 ≤ (2000259306315487/2000000000000000 : ℝ)^8229 := by
      have hnat : (12506513211647594493 : ℕ)^2048*2000000000000000^8229 ≤ 2000259306315487^8229*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506513211647594493 12500000000000000000 2000259306315487 2000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000259306315487/2000000000000000 : ℝ)) (X := (12506513211647594493/12500000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018468627288516327/25000000000000000000 : ℝ) ≤ (2000367627463697/2000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (25018468627288516327/25000000000000000000 : ℝ)^2048 ≤ (2000367627463697/2000000000000000 : ℝ)^8229 := by
      have hnat : (25018468627288516327 : ℕ)^2048*2000000000000000^8229 ≤ 2000367627463697^8229*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018468627288516327 25000000000000000000 2000367627463697 2000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000367627463697/2000000000000000 : ℝ)) (X := (25018468627288516327/25000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1516843860372329/10000000000000000000 : ℝ) ≤ ((5555991460921587423/5558000000000000000 : ℝ)+2*(10832114821/5558000000000 : ℝ)*(1401/12500 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (5555991460921587423/5558000000000000000 : ℝ)+2*(10832114821/5558000000000 : ℝ)*(1401/12500 : ℝ)=(2000150985167277/2000000000000000 : ℝ) by norm_num, show 1+2*(1516843860372329/10000000000000000000 : ℝ)=(5001516843860372329/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18468627288516327/50000000000000000000 : ℝ)+(1516843860372329/10000000000000000000 : ℝ) ≤ ((5555991460921587423/5558000000000000000 : ℝ)+(10832114821/5558000000000 : ℝ)*((13987/100000 : ℝ)+(1401/12500 : ℝ)))^(8229/2048 : ℝ) := by
    rw [show (5555991460921587423/5558000000000000000 : ℝ)+(10832114821/5558000000000 : ℝ)*((13987/100000 : ℝ)+(1401/12500 : ℝ))=(2000259306315487/2000000000000000 : ℝ) by norm_num, show 1+(18468627288516327/50000000000000000000 : ℝ)+(1516843860372329/10000000000000000000 : ℝ)=(12506513211647594493/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18468627288516327/50000000000000000000 : ℝ) ≤ ((5555991460921587423/5558000000000000000 : ℝ)+2*(10832114821/5558000000000 : ℝ)*(13987/100000 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (5555991460921587423/5558000000000000000 : ℝ)+2*(10832114821/5558000000000 : ℝ)*(13987/100000 : ℝ)=(2000367627463697/2000000000000000 : ℝ) by norm_num, show 1+2*(18468627288516327/50000000000000000000 : ℝ)=(25018468627288516327/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5555991460921587423/5558000000000000000 : ℝ)*(X 1 0+X 2 0)+(10832114821/5558000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (5555991460921587423/5558000000000000000 : ℝ)) (alpha := (10832114821/5558000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5555991460921587423/5558000000000000000 : ℝ)*(X 0 1+X 2 1)+(10832114821/5558000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (5555991460921587423/5558000000000000000 : ℝ)) (alpha := (10832114821/5558000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5555991460921587423/5558000000000000000 : ℝ)*(X 0 2+X 1 2)+(10832114821/5558000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (5555991460921587423/5558000000000000000 : ℝ)) (alpha := (10832114821/5558000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-443626051/2000000000 : ℝ)*X 0 0+(134871533/250000000 : ℝ)*X 0 1+(2631951947/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345037871/10000000000 : ℝ)*X 1 0+(-2284581943/10000000000 : ℝ)*X 1 1+(5263903823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345037819/10000000000 : ℝ)*X 2 0+(2631951947/5000000000 : ℝ)*X 2 1+(-2284581919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379679381/10000000000 : ℝ)*X 0 0+(4253984447/10000000000 : ℝ)*X 0 1+(563645761/1250000000 : ℝ)*X 0 2+(4379679381/10000000000 : ℝ)*X 1 0+(4253984447/10000000000 : ℝ)*X 1 1+(563645761/1250000000 : ℝ)*X 1 2+(4379679381/10000000000 : ℝ)*X 2 0+(4253984447/10000000000 : ℝ)*X 2 1+(563645761/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2218135337/10000000000 : ℝ)*X 0 0+(658028957/1250000000 : ℝ)*X 0 1+(2697266211/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106242583/200000000 : ℝ)*X 1 0+(-538488411/2500000000 : ℝ)*X 1 1+(5394532303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312129503/10000000000 : ℝ)*X 2 0+(1348633087/2500000000 : ℝ)*X 2 1+(-2153953107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875937891/2000000000 : ℝ)*X 0 0+(901705533/2000000000 : ℝ)*X 0 1+(4254625107/10000000000 : ℝ)*X 0 2+(875937891/2000000000 : ℝ)*X 1 0+(901705533/2000000000 : ℝ)*X 1 1+(4254625107/10000000000 : ℝ)*X 1 2+(875937891/2000000000 : ℝ)*X 2 0+(901705533/2000000000 : ℝ)*X 2 1+(4254625107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6123863170266719652437631/1588000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189744791/20000000000000 : ℝ)*(base19) + (825683941/100000000000000 : ℝ)*(base23) + (1628597/6250000000000 : ℝ)*(lower2) + (356379/390625000000 : ℝ)*(upper3) + (15707731/20000000000000 : ℝ)*(upper5) + (231098379855693/4000000000000 : ℝ)*(major0) + (231098379855693/4000000000000 : ℝ)*(major1) + (231098379855693/4000000000000 : ℝ)*(major2) + (7636093256043189/100000000000000 : ℝ)*(sp0) + (95451444623437/1250000000000 : ℝ)*(sp1) + (3818057846457487/50000000000000 : ℝ)*(sp2) + (3918789690699519/100000000000000 : ℝ)*(sp3) + (11631277863/50000000000000 : ℝ)*(sp4) + (12654941641/100000000000000 : ℝ)*(sp7) + (97970058641029/2500000000000 : ℝ)*(f.failure) + (1527223303719783/20000000000000 : ℝ)*(f.sum) + (750614276561/397000000000000000000000000 : ℝ)*base65 + (29291776371694123/3176000000000000000000000000000 : ℝ)*base68 + (13318622361177877/3176000000000000000000000000000 : ℝ)*base69 + (39571321382254123/3176000000000000000000000000000 : ℝ)*base72 + (413706218621/99250000000000000000000000 : ℝ)*base73 + (103904666684585877/3176000000000000000000000000000 : ℝ)*base75 + (34638331332350123/3176000000000000000000000000000 : ℝ)*base78 + (678230107214123/3176000000000000000000000000000 : ℝ)*base80 + (33157220009/397000000000000000000000000 : ℝ)*base81 + (560603/125000000000000000000 : ℝ)*base89 + (560603/125000000000000000000 : ℝ)*base91 + (560603/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (349465102000923318213362889/39700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1535670171/100000000000000 : ℝ)*(base19) + (1299559959/50000000000000 : ℝ)*(base23) + (262427231/100000000000000 : ℝ)*(upper3) + (16260141/12500000000000 : ℝ)*(lower4) + (17491441/20000000000000 : ℝ)*(upper5) + (5806536928320711/100000000000000 : ℝ)*(major0) + (5806536928320711/100000000000000 : ℝ)*(major1) + (5806536928320711/100000000000000 : ℝ)*(major2) + (1691311791/6250000000000 : ℝ)*(sp1) + (76874156601/100000000000000 : ℝ)*(sp2) + (3837274119624651/50000000000000 : ℝ)*(sp4) + (306980785703619/4000000000000 : ℝ)*(sp5) + (7674468765972783/100000000000000 : ℝ)*(sp6) + (1969262661985267/50000000000000 : ℝ)*(sp7) + (1969262661985267/50000000000000 : ℝ)*(f.failure) + (3837274119624651/50000000000000 : ℝ)*(f.sum) + (3525702876687/1389500000000000000000000000 : ℝ)*base66 + (4308281987511417753/555800000000000000000000000000000 : ℝ)*base67 + (3394024691223417753/555800000000000000000000000000000 : ℝ)*base69 + (2183275521442217753/555800000000000000000000000000000 : ℝ)*base71 + (382772850919/347375000000000000000000000 : ℝ)*base73 + (3457510185333217753/555800000000000000000000000000000 : ℝ)*base75 + (870713558178617753/555800000000000000000000000000000 : ℝ)*base77 + (8595453810148617753/555800000000000000000000000000000 : ℝ)*base79 + (3327249136177/694750000000000000000000000 : ℝ)*base81 + (21695069/2500000000000000000000 : ℝ)*base89 + (21695069/2500000000000000000000 : ℝ)*base91 + (21695069/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1037_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1037_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1037_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1037_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1037_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1037_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1037_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
