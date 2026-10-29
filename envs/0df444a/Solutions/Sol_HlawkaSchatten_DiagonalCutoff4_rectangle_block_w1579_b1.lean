-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1579_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:54.116458+00:00
-- url     : https://prove2.me/submissions/356dc4f8-b31c-473e-b68a-fa1c5a91b305

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
theorem support_rectangle_w1579_s3_0 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1773169327/10000000000 : ℝ)*x 0 + (542615511/1000000000 : ℝ)*x 1 + (1043800207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1773169327/10000000000 : ℝ)^4655 ≤ (2177287427853/20000000000000 : ℝ)^3631 := by
    have hnat : (1773169327 : ℕ)^4655*20000000000000^3631 ≤ 2177287427853^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773169327 10000000000 2177287427853 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542615511/1000000000 : ℝ)^4655 ≤ (4566829151753/10000000000000 : ℝ)^3631 := by
    have hnat : (542615511 : ℕ)^4655*10000000000000^3631 ≤ 4566829151753^3631*1000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542615511 1000000000 4566829151753 10000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043800207/2000000000 : ℝ)^4655 ≤ (21722635663433/50000000000000 : ℝ)^3631 := by
    have hnat : (1043800207 : ℕ)^4655*50000000000000^3631 ≤ 21722635663433^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043800207 2000000000 21722635663433 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1773169327/10000000000 : ℝ), (542615511/1000000000 : ℝ), (1043800207/2000000000 : ℝ)] ![(2177287427853/20000000000000 : ℝ), (4566829151753/10000000000000 : ℝ), (21722635663433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1773169327/10000000000 : ℝ)|^4655 ≤ (2177287427853/20000000000000 : ℝ)^3631
        have hw : |(-1773169327/10000000000 : ℝ)|=(1773169327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542615511/1000000000 : ℝ)|^4655 ≤ (4566829151753/10000000000000 : ℝ)^3631
        have hw : |(542615511/1000000000 : ℝ)|=(542615511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043800207/2000000000 : ℝ)|^4655 ≤ (21722635663433/50000000000000 : ℝ)^3631
        have hw : |(1043800207/2000000000 : ℝ)|=(1043800207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s3_1 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133700837/250000000 : ℝ)*x 0 + (-187916257/1000000000 : ℝ)*x 1 + (2609500503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133700837/250000000 : ℝ)^4655 ≤ (44827086873373/100000000000000 : ℝ)^3631 := by
    have hnat : (133700837 : ℕ)^4655*100000000000000^3631 ≤ 44827086873373^3631*250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133700837 250000000 44827086873373 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187916257/1000000000 : ℝ)^4655 ≤ (11727642094831/100000000000000 : ℝ)^3631 := by
    have hnat : (187916257 : ℕ)^4655*100000000000000^3631 ≤ 11727642094831^3631*1000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187916257 1000000000 11727642094831 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609500503/5000000000 : ℝ)^4655 ≤ (1357664719293/3125000000000 : ℝ)^3631 := by
    have hnat : (2609500503 : ℕ)^4655*3125000000000^3631 ≤ 1357664719293^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609500503 5000000000 1357664719293 3125000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133700837/250000000 : ℝ), (-187916257/1000000000 : ℝ), (2609500503/5000000000 : ℝ)] ![(44827086873373/100000000000000 : ℝ), (11727642094831/100000000000000 : ℝ), (1357664719293/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133700837/250000000 : ℝ)|^4655 ≤ (44827086873373/100000000000000 : ℝ)^3631
        have hw : |(133700837/250000000 : ℝ)|=(133700837/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187916257/1000000000 : ℝ)|^4655 ≤ (11727642094831/100000000000000 : ℝ)^3631
        have hw : |(-187916257/1000000000 : ℝ)|=(187916257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609500503/5000000000 : ℝ)|^4655 ≤ (1357664719293/3125000000000 : ℝ)^3631
        have hw : |(2609500503/5000000000 : ℝ)|=(2609500503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s3_2 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668504193/1250000000 : ℝ)*x 0 + (2609500453/5000000000 : ℝ)*x 1 + (-1879162617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668504193/1250000000 : ℝ)^4655 ≤ (22413543780553/50000000000000 : ℝ)^3631 := by
    have hnat : (668504193 : ℕ)^4655*50000000000000^3631 ≤ 22413543780553^3631*1250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668504193 1250000000 22413543780553 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609500453/5000000000 : ℝ)^4655 ≤ (4344526995017/10000000000000 : ℝ)^3631 := by
    have hnat : (2609500453 : ℕ)^4655*10000000000000^3631 ≤ 4344526995017^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609500453 5000000000 4344526995017 10000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1879162617/10000000000 : ℝ)^4655 ≤ (93821139767/800000000000 : ℝ)^3631 := by
    have hnat : (1879162617 : ℕ)^4655*800000000000^3631 ≤ 93821139767^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879162617 10000000000 93821139767 800000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668504193/1250000000 : ℝ), (2609500453/5000000000 : ℝ), (-1879162617/10000000000 : ℝ)] ![(22413543780553/50000000000000 : ℝ), (4344526995017/10000000000000 : ℝ), (93821139767/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668504193/1250000000 : ℝ)|^4655 ≤ (22413543780553/50000000000000 : ℝ)^3631
        have hw : |(668504193/1250000000 : ℝ)|=(668504193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609500453/5000000000 : ℝ)|^4655 ≤ (4344526995017/10000000000000 : ℝ)^3631
        have hw : |(2609500453/5000000000 : ℝ)|=(2609500453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1879162617/10000000000 : ℝ)|^4655 ≤ (93821139767/800000000000 : ℝ)^3631
        have hw : |(-1879162617/10000000000 : ℝ)|=(1879162617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s3_3 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239417613/10000000000 : ℝ)*x 0 + (79983131/200000000 : ℝ)*x 1 + (4491156309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239417613/10000000000 : ℝ)^4655 ≤ (8320330995989/25000000000000 : ℝ)^3631 := by
    have hnat : (4239417613 : ℕ)^4655*25000000000000^3631 ≤ 8320330995989^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239417613 10000000000 8320330995989 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79983131/200000000 : ℝ)^4655 ≤ (3860354165629/12500000000000 : ℝ)^3631 := by
    have hnat : (79983131 : ℕ)^4655*12500000000000^3631 ≤ 3860354165629^3631*200000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79983131 200000000 3860354165629 12500000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491156309/10000000000 : ℝ)^4655 ≤ (35835842680447/100000000000000 : ℝ)^3631 := by
    have hnat : (4491156309 : ℕ)^4655*100000000000000^3631 ≤ 35835842680447^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491156309 10000000000 35835842680447 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239417613/10000000000 : ℝ), (79983131/200000000 : ℝ), (4491156309/10000000000 : ℝ)] ![(8320330995989/25000000000000 : ℝ), (3860354165629/12500000000000 : ℝ), (35835842680447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239417613/10000000000 : ℝ)|^4655 ≤ (8320330995989/25000000000000 : ℝ)^3631
        have hw : |(4239417613/10000000000 : ℝ)|=(4239417613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79983131/200000000 : ℝ)|^4655 ≤ (3860354165629/12500000000000 : ℝ)^3631
        have hw : |(79983131/200000000 : ℝ)|=(79983131/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491156309/10000000000 : ℝ)|^4655 ≤ (35835842680447/100000000000000 : ℝ)^3631
        have hw : |(4491156309/10000000000 : ℝ)|=(4491156309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s3_4 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-354639501/2000000000 : ℝ)*x 0 + (5220096823/10000000000 : ℝ)*x 1 + (2712525333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (354639501/2000000000 : ℝ)^4655 ≤ (2721664732083/25000000000000 : ℝ)^3631 := by
    have hnat : (354639501 : ℕ)^4655*25000000000000^3631 ≤ 2721664732083^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354639501 2000000000 2721664732083 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220096823/10000000000 : ℝ)^4655 ≤ (21728482998339/50000000000000 : ℝ)^3631 := by
    have hnat : (5220096823 : ℕ)^4655*50000000000000^3631 ≤ 21728482998339^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220096823 10000000000 21728482998339 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712525333/5000000000 : ℝ)^4655 ≤ (9131275011659/20000000000000 : ℝ)^3631 := by
    have hnat : (2712525333 : ℕ)^4655*20000000000000^3631 ≤ 9131275011659^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712525333 5000000000 9131275011659 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-354639501/2000000000 : ℝ), (5220096823/10000000000 : ℝ), (2712525333/5000000000 : ℝ)] ![(2721664732083/25000000000000 : ℝ), (21728482998339/50000000000000 : ℝ), (9131275011659/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-354639501/2000000000 : ℝ)|^4655 ≤ (2721664732083/25000000000000 : ℝ)^3631
        have hw : |(-354639501/2000000000 : ℝ)|=(354639501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220096823/10000000000 : ℝ)|^4655 ≤ (21728482998339/50000000000000 : ℝ)^3631
        have hw : |(5220096823/10000000000 : ℝ)|=(5220096823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712525333/5000000000 : ℝ)|^4655 ≤ (9131275011659/20000000000000 : ℝ)^3631
        have hw : |(2712525333/5000000000 : ℝ)|=(2712525333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s3_5 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646584523/5000000000 : ℝ)*x 0 + (-1673112947/10000000000 : ℝ)*x 1 + (5425050547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646584523/5000000000 : ℝ)^4655 ≤ (44238378119339/100000000000000 : ℝ)^3631 := by
    have hnat : (2646584523 : ℕ)^4655*100000000000000^3631 ≤ 44238378119339^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646584523 5000000000 44238378119339 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1673112947/10000000000 : ℝ)^4655 ≤ (10105248089173/100000000000000 : ℝ)^3631 := by
    have hnat : (1673112947 : ℕ)^4655*100000000000000^3631 ≤ 10105248089173^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673112947 10000000000 10105248089173 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425050547/10000000000 : ℝ)^4655 ≤ (73050198039/160000000000 : ℝ)^3631 := by
    have hnat : (5425050547 : ℕ)^4655*160000000000^3631 ≤ 73050198039^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425050547 10000000000 73050198039 160000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646584523/5000000000 : ℝ), (-1673112947/10000000000 : ℝ), (5425050547/10000000000 : ℝ)] ![(44238378119339/100000000000000 : ℝ), (10105248089173/100000000000000 : ℝ), (73050198039/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646584523/5000000000 : ℝ)|^4655 ≤ (44238378119339/100000000000000 : ℝ)^3631
        have hw : |(2646584523/5000000000 : ℝ)|=(2646584523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1673112947/10000000000 : ℝ)|^4655 ≤ (10105248089173/100000000000000 : ℝ)^3631
        have hw : |(-1673112947/10000000000 : ℝ)|=(1673112947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425050547/10000000000 : ℝ)|^4655 ≤ (73050198039/160000000000 : ℝ)^3631
        have hw : |(5425050547/10000000000 : ℝ)|=(5425050547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s3_6 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323292373/2500000000 : ℝ)*x 0 + (2712525523/5000000000 : ℝ)*x 1 + (-334622327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323292373/2500000000 : ℝ)^4655 ≤ (44238382898061/100000000000000 : ℝ)^3631 := by
    have hnat : (1323292373 : ℕ)^4655*100000000000000^3631 ≤ 44238382898061^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323292373 2500000000 44238382898061 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712525523/5000000000 : ℝ)^4655 ≤ (45656379158209/100000000000000 : ℝ)^3631 := by
    have hnat : (2712525523 : ℕ)^4655*100000000000000^3631 ≤ 45656379158209^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712525523 5000000000 45656379158209 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334622327/2000000000 : ℝ)^4655 ≤ (505261896511/5000000000000 : ℝ)^3631 := by
    have hnat : (334622327 : ℕ)^4655*5000000000000^3631 ≤ 505261896511^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334622327 2000000000 505261896511 5000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323292373/2500000000 : ℝ), (2712525523/5000000000 : ℝ), (-334622327/2000000000 : ℝ)] ![(44238382898061/100000000000000 : ℝ), (45656379158209/100000000000000 : ℝ), (505261896511/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323292373/2500000000 : ℝ)|^4655 ≤ (44238382898061/100000000000000 : ℝ)^3631
        have hw : |(1323292373/2500000000 : ℝ)|=(1323292373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712525523/5000000000 : ℝ)|^4655 ≤ (45656379158209/100000000000000 : ℝ)^3631
        have hw : |(2712525523/5000000000 : ℝ)|=(2712525523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334622327/2000000000 : ℝ)|^4655 ≤ (505261896511/5000000000000 : ℝ)^3631
        have hw : |(-334622327/2000000000 : ℝ)|=(334622327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s3_7 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239482239/10000000000 : ℝ)*x 0 + (2244276541/5000000000 : ℝ)*x 1 + (2000890103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239482239/10000000000 : ℝ)^4655 ≤ (33281974407183/100000000000000 : ℝ)^3631 := by
    have hnat : (4239482239 : ℕ)^4655*100000000000000^3631 ≤ 33281974407183^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239482239 10000000000 33281974407183 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244276541/5000000000 : ℝ)^4655 ≤ (35809215239831/100000000000000 : ℝ)^3631 := by
    have hnat : (2244276541 : ℕ)^4655*100000000000000^3631 ≤ 35809215239831^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244276541 5000000000 35809215239831 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2000890103/5000000000 : ℝ)^4655 ≤ (30908810339039/100000000000000 : ℝ)^3631 := by
    have hnat : (2000890103 : ℕ)^4655*100000000000000^3631 ≤ 30908810339039^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000890103 5000000000 30908810339039 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239482239/10000000000 : ℝ), (2244276541/5000000000 : ℝ), (2000890103/5000000000 : ℝ)] ![(33281974407183/100000000000000 : ℝ), (35809215239831/100000000000000 : ℝ), (30908810339039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239482239/10000000000 : ℝ)|^4655 ≤ (33281974407183/100000000000000 : ℝ)^3631
        have hw : |(4239482239/10000000000 : ℝ)|=(4239482239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244276541/5000000000 : ℝ)|^4655 ≤ (35809215239831/100000000000000 : ℝ)^3631
        have hw : |(2244276541/5000000000 : ℝ)|=(2244276541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2000890103/5000000000 : ℝ)|^4655 ≤ (30908810339039/100000000000000 : ℝ)^3631
        have hw : |(2000890103/5000000000 : ℝ)|=(2000890103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1579_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3947/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3103/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3947/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10869/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3947/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10869/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3947/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10869/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3947/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10869/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3947/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10869/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3947/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10869/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10869/100000 : ℝ) ^ (4653/1024 : ℝ) ≤ (4173478683929629/100000000000000000000 : ℝ) := by
    have hpowers : (10869/100000 : ℝ)^4653 ≤ (4173478683929629/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10869 : ℕ)^4653*100000000000000000000^1024 ≤ 4173478683929629^1024*100000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10869 100000 4173478683929629 100000000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10869/100000 : ℝ)) (X := (4173478683929629/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3947/25000 : ℝ) ^ (4653/1024 : ℝ) ≤ (11381834562659239/50000000000000000000 : ℝ) := by
    have hpowers : (3947/25000 : ℝ)^4653 ≤ (11381834562659239/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3947 : ℕ)^4653*50000000000000000000^1024 ≤ 11381834562659239^1024*25000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3947 25000 11381834562659239 50000000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3947/25000 : ℝ)) (X := (11381834562659239/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004173478683929629/50000000000000000000 : ℝ) ≤ (10000183688075299/10000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (50004173478683929629/50000000000000000000 : ℝ)^1024 ≤ (10000183688075299/10000000000000000 : ℝ)^4653 := by
      have hnat : (50004173478683929629 : ℕ)^1024*10000000000000000^4653 ≤ 10000183688075299^4653*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004173478683929629 50000000000000000000 10000183688075299 10000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000183688075299/10000000000000000 : ℝ)) (X := (50004173478683929629/50000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026937147809248107/100000000000000000000 : ℝ) ≤ (500029637591119/500000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (100026937147809248107/100000000000000000000 : ℝ)^1024 ≤ (500029637591119/500000000000000 : ℝ)^4653 := by
      have hnat : (100026937147809248107 : ℕ)^1024*500000000000000^4653 ≤ 500029637591119^4653*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026937147809248107 100000000000000000000 500029637591119 500000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500029637591119/500000000000000 : ℝ)) (X := (100026937147809248107/100000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011381834562659239/25000000000000000000 : ℝ) ≤ (10001001815569461/10000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (25011381834562659239/25000000000000000000 : ℝ)^1024 ≤ (10001001815569461/10000000000000000 : ℝ)^4653 := by
      have hnat : (25011381834562659239 : ℕ)^1024*10000000000000000^4653 ≤ 10001001815569461^4653*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011381834562659239 25000000000000000000 10001001815569461 10000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001001815569461/10000000000000000 : ℝ)) (X := (25011381834562659239/25000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4173478683929629/100000000000000000000 : ℝ) ≤ ((49182011333908349003/49190000000000000000 : ℝ)+2*(409063747081/491900000000000 : ℝ)*(10869/100000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (49182011333908349003/49190000000000000000 : ℝ)+2*(409063747081/491900000000000 : ℝ)*(10869/100000 : ℝ)=(10000183688075299/10000000000000000 : ℝ) by norm_num, show 1+2*(4173478683929629/100000000000000000000 : ℝ)=(50004173478683929629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11381834562659239/50000000000000000000 : ℝ)+(4173478683929629/100000000000000000000 : ℝ) ≤ ((49182011333908349003/49190000000000000000 : ℝ)+(409063747081/491900000000000 : ℝ)*((3947/25000 : ℝ)+(10869/100000 : ℝ)))^(4653/1024 : ℝ) := by
    rw [show (49182011333908349003/49190000000000000000 : ℝ)+(409063747081/491900000000000 : ℝ)*((3947/25000 : ℝ)+(10869/100000 : ℝ))=(500029637591119/500000000000000 : ℝ) by norm_num, show 1+(11381834562659239/50000000000000000000 : ℝ)+(4173478683929629/100000000000000000000 : ℝ)=(100026937147809248107/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11381834562659239/50000000000000000000 : ℝ) ≤ ((49182011333908349003/49190000000000000000 : ℝ)+2*(409063747081/491900000000000 : ℝ)*(3947/25000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (49182011333908349003/49190000000000000000 : ℝ)+2*(409063747081/491900000000000 : ℝ)*(3947/25000 : ℝ)=(10001001815569461/10000000000000000 : ℝ) by norm_num, show 1+2*(11381834562659239/50000000000000000000 : ℝ)=(25011381834562659239/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (49182011333908349003/49190000000000000000 : ℝ)*(X 1 0+X 2 0)+(409063747081/491900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (10869/100000 : ℝ)) (hi := (3947/25000 : ℝ)) (c := (49182011333908349003/49190000000000000000 : ℝ)) (alpha := (409063747081/491900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (49182011333908349003/49190000000000000000 : ℝ)*(X 0 1+X 2 1)+(409063747081/491900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (10869/100000 : ℝ)) (hi := (3947/25000 : ℝ)) (c := (49182011333908349003/49190000000000000000 : ℝ)) (alpha := (409063747081/491900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (49182011333908349003/49190000000000000000 : ℝ)*(X 0 2+X 1 2)+(409063747081/491900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (10869/100000 : ℝ)) (hi := (3947/25000 : ℝ)) (c := (49182011333908349003/49190000000000000000 : ℝ)) (alpha := (409063747081/491900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1773169327/10000000000 : ℝ)*X 0 0+(542615511/1000000000 : ℝ)*X 0 1+(1043800207/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133700837/250000000 : ℝ)*X 1 0+(-187916257/1000000000 : ℝ)*X 1 1+(2609500503/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668504193/1250000000 : ℝ)*X 2 0+(2609500453/5000000000 : ℝ)*X 2 1+(-1879162617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4239417613/10000000000 : ℝ)*X 0 0+(79983131/200000000 : ℝ)*X 0 1+(4491156309/10000000000 : ℝ)*X 0 2+(4239417613/10000000000 : ℝ)*X 1 0+(79983131/200000000 : ℝ)*X 1 1+(4491156309/10000000000 : ℝ)*X 1 2+(4239417613/10000000000 : ℝ)*X 2 0+(79983131/200000000 : ℝ)*X 2 1+(4491156309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-354639501/2000000000 : ℝ)*X 0 0+(5220096823/10000000000 : ℝ)*X 0 1+(2712525333/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646584523/5000000000 : ℝ)*X 1 0+(-1673112947/10000000000 : ℝ)*X 1 1+(5425050547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323292373/2500000000 : ℝ)*X 2 0+(2712525523/5000000000 : ℝ)*X 2 1+(-334622327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4239482239/10000000000 : ℝ)*X 0 0+(2244276541/5000000000 : ℝ)*X 0 1+(2000890103/5000000000 : ℝ)*X 0 2+(4239482239/10000000000 : ℝ)*X 1 0+(2244276541/5000000000 : ℝ)*X 1 1+(2000890103/5000000000 : ℝ)*X 1 2+(4239482239/10000000000 : ℝ)*X 2 0+(2244276541/5000000000 : ℝ)*X 2 1+(2000890103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (894096892104818631286623669/122975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129813649/10000000000000 : ℝ)*(base19) + (134687611/10000000000000 : ℝ)*(base23) + (45033567/25000000000000 : ℝ)*(upper3) + (1207257/25000000000000 : ℝ)*(upper4) + (135320591/100000000000000 : ℝ)*(upper5) + (342995357739259/10000000000000 : ℝ)*(major0) + (342995357739259/10000000000000 : ℝ)*(major1) + (342995357739259/10000000000000 : ℝ)*(major2) + (4827346219451939/100000000000000 : ℝ)*(sp0) + (4827365620468879/100000000000000 : ℝ)*(sp1) + (2413682785864629/50000000000000 : ℝ)*(sp2) + (1016265143916877/50000000000000 : ℝ)*(sp3) + (2069915343/10000000000000 : ℝ)*(sp4) + (2426498527/25000000000000 : ℝ)*(sp7) + (2032539993827863/100000000000000 : ℝ)*(f.failure) + (4827366918605369/100000000000000 : ℝ)*(f.sum) + (15017305325649/4919000000000000000000000000 : ℝ)*base65 + (6750554308506108777/491900000000000000000000000000000 : ℝ)*base67 + (4809673951024408777/491900000000000000000000000000000 : ℝ)*base69 + (1515565029609908777/491900000000000000000000000000000 : ℝ)*base71 + (10719285122141/1229750000000000000000000000 : ℝ)*base73 + (1926524569859308777/491900000000000000000000000000000 : ℝ)*base75 + (5608093621209108777/491900000000000000000000000000000 : ℝ)*base77 + (1391323613293091223/491900000000000000000000000000000 : ℝ)*base80 + (19476475780923/2459500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (24688629/10000000000000000000000 : ℝ)*base89 + (24688629/10000000000000000000000 : ℝ)*base91 + (24688629/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87405533947876068250588773/122975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486415961/100000000000000 : ℝ)*(base19) + (2328700633/100000000000000 : ℝ)*(base23) + (51618389/10000000000000 : ℝ)*(upper2) + (33312473/20000000000000 : ℝ)*(upper5) + (346674765532803/10000000000000 : ℝ)*(major0) + (346674765532803/10000000000000 : ℝ)*(major1) + (346674765532803/10000000000000 : ℝ)*(major2) + (1233897151/50000000000000 : ℝ)*(sp0) + (104499019/1000000000000 : ℝ)*(sp1) + (5444207153/10000000000000 : ℝ)*(sp2) + (975829839288731/20000000000000 : ℝ)*(sp4) + (975828145584019/20000000000000 : ℝ)*(sp5) + (4879094893465793/100000000000000 : ℝ)*(sp6) + (4012389888137/195312500000 : ℝ)*(sp7) + (4012389888137/195312500000 : ℝ)*(f.failure) + (1219787916059489/25000000000000 : ℝ)*(f.sum) + (13007623732933/4919000000000000000000000000 : ℝ)*base65 + (2263723993873554591/491900000000000000000000000000000 : ℝ)*base68 + (1327704130131545409/491900000000000000000000000000000 : ℝ)*base69 + (2149317163239745409/491900000000000000000000000000000 : ℝ)*base71 + (7835271068631/4919000000000000000000000000 : ℝ)*base74 + (3020318962808045409/491900000000000000000000000000000 : ℝ)*base75 + (4997615854898345409/491900000000000000000000000000000 : ℝ)*base77 + (2716033343047745409/491900000000000000000000000000000 : ℝ)*base79 + (1439647883821/983800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (30001/4882812500000000000 : ℝ)*base90 + (30001/4882812500000000000 : ℝ)*base92 + (30001/4882812500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1579_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3947/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3103/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1579_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1579_s4_0 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-443342943/2500000000 : ℝ)*x 0 + (339049463/625000000 : ℝ)*x 1 + (1305057597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443342943/2500000000 : ℝ)^4655 ≤ (2722007651537/25000000000000 : ℝ)^3631 := by
    have hnat : (443342943 : ℕ)^4655*25000000000000^3631 ≤ 2722007651537^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443342943 2500000000 2722007651537 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339049463/625000000 : ℝ)^4655 ≤ (45653577879/100000000000 : ℝ)^3631 := by
    have hnat : (339049463 : ℕ)^4655*100000000000^3631 ≤ 45653577879^3631*625000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339049463 625000000 45653577879 100000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305057597/2500000000 : ℝ)^4655 ≤ (1738335660037/4000000000000 : ℝ)^3631 := by
    have hnat : (1305057597 : ℕ)^4655*4000000000000^3631 ≤ 1738335660037^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305057597 2500000000 1738335660037 4000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443342943/2500000000 : ℝ), (339049463/625000000 : ℝ), (1305057597/2500000000 : ℝ)] ![(2722007651537/25000000000000 : ℝ), (45653577879/100000000000 : ℝ), (1738335660037/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443342943/2500000000 : ℝ)|^4655 ≤ (2722007651537/25000000000000 : ℝ)^3631
        have hw : |(-443342943/2500000000 : ℝ)|=(443342943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339049463/625000000 : ℝ)|^4655 ≤ (45653577879/100000000000 : ℝ)^3631
        have hw : |(339049463/625000000 : ℝ)|=(339049463/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305057597/2500000000 : ℝ)|^4655 ≤ (1738335660037/4000000000000 : ℝ)^3631
        have hw : |(1305057597/2500000000 : ℝ)|=(1305057597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s4_1 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069534339/2000000000 : ℝ)*x 0 + (-1878008471/10000000000 : ℝ)*x 1 + (652528801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069534339/2000000000 : ℝ)^4655 ≤ (22411599615757/50000000000000 : ℝ)^3631 := by
    have hnat : (1069534339 : ℕ)^4655*50000000000000^3631 ≤ 22411599615757^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069534339 2000000000 22411599615757 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1878008471/10000000000 : ℝ)^4655 ≤ (5859204521921/50000000000000 : ℝ)^3631 := by
    have hnat : (1878008471 : ℕ)^4655*50000000000000^3631 ≤ 5859204521921^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878008471 10000000000 5859204521921 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652528801/1250000000 : ℝ)^4655 ≤ (2172919585719/5000000000000 : ℝ)^3631 := by
    have hnat : (652528801 : ℕ)^4655*5000000000000^3631 ≤ 2172919585719^3631*1250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652528801 1250000000 2172919585719 5000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069534339/2000000000 : ℝ), (-1878008471/10000000000 : ℝ), (652528801/1250000000 : ℝ)] ![(22411599615757/50000000000000 : ℝ), (5859204521921/50000000000000 : ℝ), (2172919585719/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069534339/2000000000 : ℝ)|^4655 ≤ (22411599615757/50000000000000 : ℝ)^3631
        have hw : |(1069534339/2000000000 : ℝ)|=(1069534339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1878008471/10000000000 : ℝ)|^4655 ≤ (5859204521921/50000000000000 : ℝ)^3631
        have hw : |(-1878008471/10000000000 : ℝ)|=(1878008471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652528801/1250000000 : ℝ)|^4655 ≤ (2172919585719/5000000000000 : ℝ)^3631
        have hw : |(652528801/1250000000 : ℝ)|=(652528801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s4_2 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347671703/10000000000 : ℝ)*x 0 + (815661/1562500 : ℝ)*x 1 + (-1878008471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347671703/10000000000 : ℝ)^4655 ≤ (44823199317479/100000000000000 : ℝ)^3631 := by
    have hnat : (5347671703 : ℕ)^4655*100000000000000^3631 ≤ 44823199317479^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347671703 10000000000 44823199317479 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (815661/1562500 : ℝ)^4655 ≤ (21729195814499/50000000000000 : ℝ)^3631 := by
    have hnat : (815661 : ℕ)^4655*50000000000000^3631 ≤ 21729195814499^3631*1562500^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815661 1562500 21729195814499 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1878008471/10000000000 : ℝ)^4655 ≤ (5859204521921/50000000000000 : ℝ)^3631 := by
    have hnat : (1878008471 : ℕ)^4655*50000000000000^3631 ≤ 5859204521921^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878008471 10000000000 5859204521921 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347671703/10000000000 : ℝ), (815661/1562500 : ℝ), (-1878008471/10000000000 : ℝ)] ![(44823199317479/100000000000000 : ℝ), (21729195814499/50000000000000 : ℝ), (5859204521921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347671703/10000000000 : ℝ)|^4655 ≤ (44823199317479/100000000000000 : ℝ)^3631
        have hw : |(5347671703/10000000000 : ℝ)|=(5347671703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(815661/1562500 : ℝ)|^4655 ≤ (21729195814499/50000000000000 : ℝ)^3631
        have hw : |(815661/1562500 : ℝ)|=(815661/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1878008471/10000000000 : ℝ)|^4655 ≤ (5859204521921/50000000000000 : ℝ)^3631
        have hw : |(-1878008471/10000000000 : ℝ)|=(1878008471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s4_3 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (847909231/2000000000 : ℝ)*x 0 + (800444361/2000000000 : ℝ)*x 1 + (56100783/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847909231/2000000000 : ℝ)^4655 ≤ (33282617687421/100000000000000 : ℝ)^3631 := by
    have hnat : (847909231 : ℕ)^4655*100000000000000^3631 ≤ 33282617687421^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847909231 2000000000 33282617687421 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (800444361/2000000000 : ℝ)^4655 ≤ (3091318311607/10000000000000 : ℝ)^3631 := by
    have hnat : (800444361 : ℕ)^4655*10000000000000^3631 ≤ 3091318311607^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800444361 2000000000 3091318311607 10000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56100783/125000000 : ℝ)^4655 ≤ (35804199178503/100000000000000 : ℝ)^3631 := by
    have hnat : (56100783 : ℕ)^4655*100000000000000^3631 ≤ 35804199178503^3631*125000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56100783 125000000 35804199178503 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847909231/2000000000 : ℝ), (800444361/2000000000 : ℝ), (56100783/125000000 : ℝ)] ![(33282617687421/100000000000000 : ℝ), (3091318311607/10000000000000 : ℝ), (35804199178503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847909231/2000000000 : ℝ)|^4655 ≤ (33282617687421/100000000000000 : ℝ)^3631
        have hw : |(847909231/2000000000 : ℝ)|=(847909231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(800444361/2000000000 : ℝ)|^4655 ≤ (3091318311607/10000000000000 : ℝ)^3631
        have hw : |(800444361/2000000000 : ℝ)|=(800444361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56100783/125000000 : ℝ)|^4655 ≤ (35804199178503/100000000000000 : ℝ)^3631
        have hw : |(56100783/125000000 : ℝ)|=(56100783/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s4_4 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-177339889/1000000000 : ℝ)*x 0 + (1044259827/2000000000 : ℝ)*x 1 + (5423714339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (177339889/1000000000 : ℝ)^4655 ≤ (1361030507351/12500000000000 : ℝ)^3631 := by
    have hnat : (177339889 : ℕ)^4655*12500000000000^3631 ≤ 1361030507351^3631*1000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177339889 1000000000 1361030507351 12500000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044259827/2000000000 : ℝ)^4655 ≤ (21734899164021/50000000000000 : ℝ)^3631 := by
    have hnat : (1044259827 : ℕ)^4655*50000000000000^3631 ≤ 21734899164021^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044259827 2000000000 21734899164021 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423714339/10000000000 : ℝ)^4655 ≤ (45641957599381/100000000000000 : ℝ)^3631 := by
    have hnat : (5423714339 : ℕ)^4655*100000000000000^3631 ≤ 45641957599381^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423714339 10000000000 45641957599381 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-177339889/1000000000 : ℝ), (1044259827/2000000000 : ℝ), (5423714339/10000000000 : ℝ)] ![(1361030507351/12500000000000 : ℝ), (21734899164021/50000000000000 : ℝ), (45641957599381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-177339889/1000000000 : ℝ)|^4655 ≤ (1361030507351/12500000000000 : ℝ)^3631
        have hw : |(-177339889/1000000000 : ℝ)|=(177339889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044259827/2000000000 : ℝ)|^4655 ≤ (21734899164021/50000000000000 : ℝ)^3631
        have hw : |(1044259827/2000000000 : ℝ)|=(1044259827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423714339/10000000000 : ℝ)|^4655 ≤ (45641957599381/100000000000000 : ℝ)^3631
        have hw : |(5423714339/10000000000 : ℝ)|=(5423714339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s4_5 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293494151/10000000000 : ℝ)*x 0 + (-837262151/5000000000 : ℝ)*x 1 + (1355928659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293494151/10000000000 : ℝ)^4655 ≤ (5530232690851/12500000000000 : ℝ)^3631 := by
    have hnat : (5293494151 : ℕ)^4655*12500000000000^3631 ≤ 5530232690851^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293494151 10000000000 5530232690851 12500000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837262151/5000000000 : ℝ)^4655 ≤ (126452220737/1250000000000 : ℝ)^3631 := by
    have hnat : (837262151 : ℕ)^4655*1250000000000^3631 ≤ 126452220737^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837262151 5000000000 126452220737 1250000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355928659/2500000000 : ℝ)^4655 ≤ (11410490200891/25000000000000 : ℝ)^3631 := by
    have hnat : (1355928659 : ℕ)^4655*25000000000000^3631 ≤ 11410490200891^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355928659 2500000000 11410490200891 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293494151/10000000000 : ℝ), (-837262151/5000000000 : ℝ), (1355928659/2500000000 : ℝ)] ![(5530232690851/12500000000000 : ℝ), (126452220737/1250000000000 : ℝ), (11410490200891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293494151/10000000000 : ℝ)|^4655 ≤ (5530232690851/12500000000000 : ℝ)^3631
        have hw : |(5293494151/10000000000 : ℝ)|=(5293494151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-837262151/5000000000 : ℝ)|^4655 ≤ (126452220737/1250000000000 : ℝ)^3631
        have hw : |(-837262151/5000000000 : ℝ)|=(837262151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355928659/2500000000 : ℝ)|^4655 ≤ (11410490200891/25000000000000 : ℝ)^3631
        have hw : |(1355928659/2500000000 : ℝ)|=(1355928659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s4_6 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293493677/10000000000 : ℝ)*x 0 + (5423715071/10000000000 : ℝ)*x 1 + (-26164443/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293493677/10000000000 : ℝ)^4655 ≤ (44241856447989/100000000000000 : ℝ)^3631 := by
    have hnat : (5293493677 : ℕ)^4655*100000000000000^3631 ≤ 44241856447989^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293493677 10000000000 44241856447989 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423715071/10000000000 : ℝ)^4655 ≤ (570524568707/1250000000000 : ℝ)^3631 := by
    have hnat : (5423715071 : ℕ)^4655*1250000000000^3631 ≤ 570524568707^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423715071 10000000000 570524568707 1250000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26164443/156250000 : ℝ)^4655 ≤ (39516320493/390625000000 : ℝ)^3631 := by
    have hnat : (26164443 : ℕ)^4655*390625000000^3631 ≤ 39516320493^3631*156250000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26164443 156250000 39516320493 390625000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293493677/10000000000 : ℝ), (5423715071/10000000000 : ℝ), (-26164443/156250000 : ℝ)] ![(44241856447989/100000000000000 : ℝ), (570524568707/1250000000000 : ℝ), (39516320493/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293493677/10000000000 : ℝ)|^4655 ≤ (44241856447989/100000000000000 : ℝ)^3631
        have hw : |(5293493677/10000000000 : ℝ)|=(5293493677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423715071/10000000000 : ℝ)|^4655 ≤ (570524568707/1250000000000 : ℝ)^3631
        have hw : |(5423715071/10000000000 : ℝ)|=(5423715071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26164443/156250000 : ℝ)|^4655 ≤ (39516320493/390625000000 : ℝ)^3631
        have hw : |(-26164443/156250000 : ℝ)|=(26164443/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s4_7 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059902381/2500000000 : ℝ)*x 0 + (1121380923/2500000000 : ℝ)*x 1 + (4004779283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059902381/2500000000 : ℝ)^4655 ≤ (33283255465097/100000000000000 : ℝ)^3631 := by
    have hnat : (1059902381 : ℕ)^4655*100000000000000^3631 ≤ 33283255465097^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059902381 2500000000 33283255465097 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121380923/2500000000 : ℝ)^4655 ≤ (7155646843823/20000000000000 : ℝ)^3631 := by
    have hnat : (1121380923 : ℕ)^4655*20000000000000^3631 ≤ 7155646843823^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121380923 2500000000 7155646843823 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4004779283/10000000000 : ℝ)^4655 ≤ (15469255153971/50000000000000 : ℝ)^3631 := by
    have hnat : (4004779283 : ℕ)^4655*50000000000000^3631 ≤ 15469255153971^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4004779283 10000000000 15469255153971 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059902381/2500000000 : ℝ), (1121380923/2500000000 : ℝ), (4004779283/10000000000 : ℝ)] ![(33283255465097/100000000000000 : ℝ), (7155646843823/20000000000000 : ℝ), (15469255153971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059902381/2500000000 : ℝ)|^4655 ≤ (33283255465097/100000000000000 : ℝ)^3631
        have hw : |(1059902381/2500000000 : ℝ)|=(1059902381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121380923/2500000000 : ℝ)|^4655 ≤ (7155646843823/20000000000000 : ℝ)^3631
        have hw : |(1121380923/2500000000 : ℝ)|=(1121380923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4004779283/10000000000 : ℝ)|^4655 ≤ (15469255153971/50000000000000 : ℝ)^3631
        have hw : |(4004779283/10000000000 : ℝ)|=(4004779283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1579_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3103/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11147/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15487/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3103/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3103/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3103/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3103/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3103/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3103/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11121/100000 : ℝ) ^ (4653/1024 : ℝ) ≤ (23157932338981/500000000000000000 : ℝ) := by
    have hpowers : (11121/100000 : ℝ)^4653 ≤ (23157932338981/500000000000000000 : ℝ)^1024 := by
      have hnat : (11121 : ℕ)^4653*500000000000000000^1024 ≤ 23157932338981^1024*100000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11121 100000 23157932338981 500000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11121/100000 : ℝ)) (X := (23157932338981/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3103/20000 : ℝ) ^ (4653/1024 : ℝ) ≤ (21029083415707907/100000000000000000000 : ℝ) := by
    have hpowers : (3103/20000 : ℝ)^4653 ≤ (21029083415707907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3103 : ℕ)^4653*100000000000000000000^1024 ≤ 21029083415707907^1024*20000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3103 20000 21029083415707907 100000000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3103/20000 : ℝ)) (X := (21029083415707907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250023157932338981/250000000000000000 : ℝ) ≤ (1250025481266013/1250000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (250023157932338981/250000000000000000 : ℝ)^1024 ≤ (1250025481266013/1250000000000000 : ℝ)^4653 := by
      have hnat : (250023157932338981 : ℕ)^1024*1250000000000000^4653 ≤ 1250025481266013^4653*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250023157932338981 250000000000000000 1250025481266013 1250000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250025481266013/1250000000000000 : ℝ)) (X := (250023157932338981/250000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025660669883504107/100000000000000000000 : ℝ) ≤ (10000564665741277/10000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (100025660669883504107/100000000000000000000 : ℝ)^1024 ≤ (10000564665741277/10000000000000000 : ℝ)^4653 := by
      have hnat : (100025660669883504107 : ℕ)^1024*10000000000000000^4653 ≤ 10000564665741277^4653*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025660669883504107 100000000000000000000 10000564665741277 10000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000564665741277/10000000000000000 : ℝ)) (X := (100025660669883504107/100000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021029083415707907/50000000000000000000 : ℝ) ≤ (200018509627089/200000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (50021029083415707907/50000000000000000000 : ℝ)^1024 ≤ (200018509627089/200000000000000 : ℝ)^4653 := by
      have hnat : (50021029083415707907 : ℕ)^1024*200000000000000^4653 ≤ 200018509627089^4653*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021029083415707907 50000000000000000000 200018509627089 200000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200018509627089/200000000000000 : ℝ)) (X := (50021029083415707907/50000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23157932338981/500000000000000000 : ℝ) ≤ ((4393287045659469511/4394000000000000000 : ℝ)+2*(360815613173/439400000000000 : ℝ)*(11121/100000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (4393287045659469511/4394000000000000000 : ℝ)+2*(360815613173/439400000000000 : ℝ)*(11121/100000 : ℝ)=(1250025481266013/1250000000000000 : ℝ) by norm_num, show 1+2*(23157932338981/500000000000000000 : ℝ)=(250023157932338981/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21029083415707907/100000000000000000000 : ℝ)+(23157932338981/500000000000000000 : ℝ) ≤ ((4393287045659469511/4394000000000000000 : ℝ)+(360815613173/439400000000000 : ℝ)*((3103/20000 : ℝ)+(11121/100000 : ℝ)))^(4653/1024 : ℝ) := by
    rw [show (4393287045659469511/4394000000000000000 : ℝ)+(360815613173/439400000000000 : ℝ)*((3103/20000 : ℝ)+(11121/100000 : ℝ))=(10000564665741277/10000000000000000 : ℝ) by norm_num, show 1+(21029083415707907/100000000000000000000 : ℝ)+(23157932338981/500000000000000000 : ℝ)=(100025660669883504107/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21029083415707907/100000000000000000000 : ℝ) ≤ ((4393287045659469511/4394000000000000000 : ℝ)+2*(360815613173/439400000000000 : ℝ)*(3103/20000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (4393287045659469511/4394000000000000000 : ℝ)+2*(360815613173/439400000000000 : ℝ)*(3103/20000 : ℝ)=(200018509627089/200000000000000 : ℝ) by norm_num, show 1+2*(21029083415707907/100000000000000000000 : ℝ)=(50021029083415707907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4393287045659469511/4394000000000000000 : ℝ)*(X 1 0+X 2 0)+(360815613173/439400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3103/20000 : ℝ)) (c := (4393287045659469511/4394000000000000000 : ℝ)) (alpha := (360815613173/439400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4393287045659469511/4394000000000000000 : ℝ)*(X 0 1+X 2 1)+(360815613173/439400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3103/20000 : ℝ)) (c := (4393287045659469511/4394000000000000000 : ℝ)) (alpha := (360815613173/439400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4393287045659469511/4394000000000000000 : ℝ)*(X 0 2+X 1 2)+(360815613173/439400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (3103/20000 : ℝ)) (c := (4393287045659469511/4394000000000000000 : ℝ)) (alpha := (360815613173/439400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-443342943/2500000000 : ℝ)*X 0 0+(339049463/625000000 : ℝ)*X 0 1+(1305057597/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069534339/2000000000 : ℝ)*X 1 0+(-1878008471/10000000000 : ℝ)*X 1 1+(652528801/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347671703/10000000000 : ℝ)*X 2 0+(815661/1562500 : ℝ)*X 2 1+(-1878008471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((847909231/2000000000 : ℝ)*X 0 0+(800444361/2000000000 : ℝ)*X 0 1+(56100783/125000000 : ℝ)*X 0 2+(847909231/2000000000 : ℝ)*X 1 0+(800444361/2000000000 : ℝ)*X 1 1+(56100783/125000000 : ℝ)*X 1 2+(847909231/2000000000 : ℝ)*X 2 0+(800444361/2000000000 : ℝ)*X 2 1+(56100783/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-177339889/1000000000 : ℝ)*X 0 0+(1044259827/2000000000 : ℝ)*X 0 1+(5423714339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293494151/10000000000 : ℝ)*X 1 0+(-837262151/5000000000 : ℝ)*X 1 1+(1355928659/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293493677/10000000000 : ℝ)*X 2 0+(5423715071/10000000000 : ℝ)*X 2 1+(-26164443/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1059902381/2500000000 : ℝ)*X 0 0+(1121380923/2500000000 : ℝ)*X 0 1+(4004779283/10000000000 : ℝ)*X 0 2+(1059902381/2500000000 : ℝ)*X 1 0+(1121380923/2500000000 : ℝ)*X 1 1+(4004779283/10000000000 : ℝ)*X 1 2+(1059902381/2500000000 : ℝ)*X 2 0+(1121380923/2500000000 : ℝ)*X 2 1+(4004779283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47481036835862820035373153/4225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1886231171/100000000000000 : ℝ)*(base19) + (55455417/3125000000000 : ℝ)*(base23) + (63621803/100000000000000 : ℝ)*(lower2) + (8676363/3125000000000 : ℝ)*(upper3) + (96699073/50000000000000 : ℝ)*(upper5) + (868361766220611/25000000000000 : ℝ)*(major0) + (868361766220611/25000000000000 : ℝ)*(major1) + (868361766220611/25000000000000 : ℝ)*(major2) + (1222137254508839/25000000000000 : ℝ)*(sp0) + (4888578274731187/100000000000000 : ℝ)*(sp1) + (2444289193194507/50000000000000 : ℝ)*(sp2) + (2058299701934371/100000000000000 : ℝ)*(sp3) + (31142927001/100000000000000 : ℝ)*(sp4) + (1736533039/12500000000000 : ℝ)*(sp7) + (2058313594198683/100000000000000 : ℝ)*(f.failure) + (2444290080481179/50000000000000 : ℝ)*(f.sum) + (2188680304267/845000000000000000000000000 : ℝ)*base65 + (7266591395182983/8450000000000000000000000000000 : ℝ)*base68 + (10742991200632983/8450000000000000000000000000000 : ℝ)*base70 + (58148672130382983/8450000000000000000000000000000 : ℝ)*base72 + (272491585243/211250000000000000000000000 : ℝ)*base73 + (105381037805682983/8450000000000000000000000000000 : ℝ)*base76 + (41791321641032983/8450000000000000000000000000000 : ℝ)*base78 + (84587135228832983/8450000000000000000000000000000 : ℝ)*base80 + (175773449483/52812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (72106689/10000000000000000000000 : ℝ)*base89 + (72106689/10000000000000000000000 : ℝ)*base91 + (72106689/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (190832147035578311692857/21970000000000000000000000000 : ℝ) := by norm_num
    linear_combination (842275723/50000000000000 : ℝ)*(base19) + (1573207079/100000000000000 : ℝ)*(base23) + (167282621/100000000000000 : ℝ)*(upper2) + (332877979/100000000000000 : ℝ)*(upper3) + (374243253/100000000000000 : ℝ)*(upper5) + (3510220535375413/100000000000000 : ℝ)*(major0) + (3510220535375413/100000000000000 : ℝ)*(major1) + (3510220535375413/100000000000000 : ℝ)*(major2) + (28736812349/100000000000000 : ℝ)*(sp1) + (15101891689/50000000000000 : ℝ)*(sp2) + (4940335769786443/100000000000000 : ℝ)*(sp4) + (617538168552831/12500000000000 : ℝ)*(sp5) + (2470151996397993/50000000000000 : ℝ)*(sp6) + (2080105011429941/100000000000000 : ℝ)*(sp7) + (2080105011429941/100000000000000 : ℝ)*(f.failure) + (4940335769786443/100000000000000 : ℝ)*(f.sum) + (69445999498131/21970000000000000000000000000 : ℝ)*base66 + (2548031621473223043/439400000000000000000000000000000 : ℝ)*base67 + (5596611862144976957/439400000000000000000000000000000 : ℝ)*base70 + (1861682425420776957/439400000000000000000000000000000 : ℝ)*base72 + (27618508844359/21970000000000000000000000000 : ℝ)*base73 + (1062812233940823043/439400000000000000000000000000000 : ℝ)*base75 + (2730217976828976957/439400000000000000000000000000000 : ℝ)*base78 + (4491862786673823043/439400000000000000000000000000000 : ℝ)*base79 + (102307767144761/21970000000000000000000000000 : ℝ)*base82 + (52317103/10000000000000000000000 : ℝ)*base89 + (52317103/10000000000000000000000 : ℝ)*base91 + (52317103/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1579_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3103/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1579_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1579_s5_0 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-886695517/5000000000 : ℝ)*x 0 + (5424660291/10000000000 : ℝ)*x 1 + (652543591/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886695517/5000000000 : ℝ)^4655 ≤ (170127847221/1562500000000 : ℝ)^3631 := by
    have hnat : (886695517 : ℕ)^4655*1562500000000^3631 ≤ 170127847221^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886695517 5000000000 170127847221 1562500000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424660291/10000000000 : ℝ)^4655 ≤ (22826081624709/50000000000000 : ℝ)^3631 := by
    have hnat : (5424660291 : ℕ)^4655*50000000000000^3631 ≤ 22826081624709^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424660291 10000000000 22826081624709 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652543591/1250000000 : ℝ)^4655 ≤ (4345965452133/10000000000000 : ℝ)^3631 := by
    have hnat : (652543591 : ℕ)^4655*10000000000000^3631 ≤ 4345965452133^3631*1250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652543591 1250000000 4345965452133 10000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-886695517/5000000000 : ℝ), (5424660291/10000000000 : ℝ), (652543591/1250000000 : ℝ)] ![(170127847221/1562500000000 : ℝ), (22826081624709/50000000000000 : ℝ), (4345965452133/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-886695517/5000000000 : ℝ)|^4655 ≤ (170127847221/1562500000000 : ℝ)^3631
        have hw : |(-886695517/5000000000 : ℝ)|=(886695517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424660291/10000000000 : ℝ)|^4655 ≤ (22826081624709/50000000000000 : ℝ)^3631
        have hw : |(5424660291/10000000000 : ℝ)|=(5424660291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652543591/1250000000 : ℝ)|^4655 ≤ (4345965452133/10000000000000 : ℝ)^3631
        have hw : |(652543591/1250000000 : ℝ)|=(652543591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s5_1 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347636789/10000000000 : ℝ)*x 0 + (-1877896629/10000000000 : ℝ)*x 1 + (5220349379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347636789/10000000000 : ℝ)^4655 ≤ (22411412072593/50000000000000 : ℝ)^3631 := by
    have hnat : (5347636789 : ℕ)^4655*50000000000000^3631 ≤ 22411412072593^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347636789 10000000000 22411412072593 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877896629/10000000000 : ℝ)^4655 ≤ (5858757183887/50000000000000 : ℝ)^3631 := by
    have hnat : (1877896629 : ℕ)^4655*50000000000000^3631 ≤ 5858757183887^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877896629 10000000000 5858757183887 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220349379/10000000000 : ℝ)^4655 ≤ (5432457683669/12500000000000 : ℝ)^3631 := by
    have hnat : (5220349379 : ℕ)^4655*12500000000000^3631 ≤ 5432457683669^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220349379 10000000000 5432457683669 12500000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347636789/10000000000 : ℝ), (-1877896629/10000000000 : ℝ), (5220349379/10000000000 : ℝ)] ![(22411412072593/50000000000000 : ℝ), (5858757183887/50000000000000 : ℝ), (5432457683669/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347636789/10000000000 : ℝ)|^4655 ≤ (22411412072593/50000000000000 : ℝ)^3631
        have hw : |(5347636789/10000000000 : ℝ)|=(5347636789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1877896629/10000000000 : ℝ)|^4655 ≤ (5858757183887/50000000000000 : ℝ)^3631
        have hw : |(-1877896629/10000000000 : ℝ)|=(1877896629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220349379/10000000000 : ℝ)|^4655 ≤ (5432457683669/12500000000000 : ℝ)^3631
        have hw : |(5220349379/10000000000 : ℝ)|=(5220349379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s5_2 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668454609/1250000000 : ℝ)*x 0 + (5220349483/10000000000 : ℝ)*x 1 + (-1877896379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668454609/1250000000 : ℝ)^4655 ≤ (44822825037071/100000000000000 : ℝ)^3631 := by
    have hnat : (668454609 : ℕ)^4655*100000000000000^3631 ≤ 44822825037071^3631*1250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668454609 1250000000 44822825037071 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220349483/10000000000 : ℝ)^4655 ≤ (339528613901/781250000000 : ℝ)^3631 := by
    have hnat : (5220349483 : ℕ)^4655*781250000000^3631 ≤ 339528613901^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220349483 10000000000 339528613901 781250000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877896379/10000000000 : ℝ)^4655 ≤ (2929378091981/25000000000000 : ℝ)^3631 := by
    have hnat : (1877896379 : ℕ)^4655*25000000000000^3631 ≤ 2929378091981^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877896379 10000000000 2929378091981 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668454609/1250000000 : ℝ), (5220349483/10000000000 : ℝ), (-1877896379/10000000000 : ℝ)] ![(44822825037071/100000000000000 : ℝ), (339528613901/781250000000 : ℝ), (2929378091981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668454609/1250000000 : ℝ)|^4655 ≤ (44822825037071/100000000000000 : ℝ)^3631
        have hw : |(668454609/1250000000 : ℝ)|=(668454609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220349483/10000000000 : ℝ)|^4655 ≤ (339528613901/781250000000 : ℝ)^3631
        have hw : |(5220349483/10000000000 : ℝ)|=(5220349483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1877896379/10000000000 : ℝ)|^4655 ≤ (2929378091981/25000000000000 : ℝ)^3631
        have hw : |(-1877896379/10000000000 : ℝ)|=(1877896379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s5_3 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239558983/10000000000 : ℝ)*x 0 + (80050367/200000000 : ℝ)*x 1 + (897552579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239558983/10000000000 : ℝ)^4655 ≤ (16641373397343/50000000000000 : ℝ)^3631 := by
    have hnat : (4239558983 : ℕ)^4655*50000000000000^3631 ≤ 16641373397343^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239558983 10000000000 16641373397343 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80050367/200000000 : ℝ)^4655 ≤ (30916119623827/100000000000000 : ℝ)^3631 := by
    have hnat : (80050367 : ℕ)^4655*100000000000000^3631 ≤ 30916119623827^3631*200000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80050367 200000000 30916119623827 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897552579/2000000000 : ℝ)^4655 ≤ (1432045342897/4000000000000 : ℝ)^3631 := by
    have hnat : (897552579 : ℕ)^4655*4000000000000^3631 ≤ 1432045342897^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897552579 2000000000 1432045342897 4000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239558983/10000000000 : ℝ), (80050367/200000000 : ℝ), (897552579/2000000000 : ℝ)] ![(16641373397343/50000000000000 : ℝ), (30916119623827/100000000000000 : ℝ), (1432045342897/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239558983/10000000000 : ℝ)|^4655 ≤ (16641373397343/50000000000000 : ℝ)^3631
        have hw : |(4239558983/10000000000 : ℝ)|=(4239558983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80050367/200000000 : ℝ)|^4655 ≤ (30916119623827/100000000000000 : ℝ)^3631
        have hw : |(80050367/200000000 : ℝ)|=(80050367/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897552579/2000000000 : ℝ)|^4655 ≤ (1432045342897/4000000000000 : ℝ)^3631
        have hw : |(897552579/2000000000 : ℝ)|=(897552579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s5_4 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-221677209/1250000000 : ℝ)*x 0 + (1044283141/2000000000 : ℝ)*x 1 + (5423585309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221677209/1250000000 : ℝ)^4655 ≤ (2722097974309/25000000000000 : ℝ)^3631 := by
    have hnat : (221677209 : ℕ)^4655*25000000000000^3631 ≤ 2722097974309^3631*1250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221677209 1250000000 2722097974309 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044283141/2000000000 : ℝ)^4655 ≤ (43471042529341/100000000000000 : ℝ)^3631 := by
    have hnat : (1044283141 : ℕ)^4655*100000000000000^3631 ≤ 43471042529341^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044283141 2000000000 43471042529341 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423585309/10000000000 : ℝ)^4655 ≤ (45640565564453/100000000000000 : ℝ)^3631 := by
    have hnat : (5423585309 : ℕ)^4655*100000000000000^3631 ≤ 45640565564453^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423585309 10000000000 45640565564453 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221677209/1250000000 : ℝ), (1044283141/2000000000 : ℝ), (5423585309/10000000000 : ℝ)] ![(2722097974309/25000000000000 : ℝ), (43471042529341/100000000000000 : ℝ), (45640565564453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221677209/1250000000 : ℝ)|^4655 ≤ (2722097974309/25000000000000 : ℝ)^3631
        have hw : |(-221677209/1250000000 : ℝ)|=(221677209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044283141/2000000000 : ℝ)|^4655 ≤ (43471042529341/100000000000000 : ℝ)^3631
        have hw : |(1044283141/2000000000 : ℝ)|=(1044283141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423585309/10000000000 : ℝ)|^4655 ≤ (45640565564453/100000000000000 : ℝ)^3631
        have hw : |(5423585309/10000000000 : ℝ)|=(5423585309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s5_5 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293525691/10000000000 : ℝ)*x 0 + (-1674660793/10000000000 : ℝ)*x 1 + (1355896331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293525691/10000000000 : ℝ)^4655 ≤ (8848439894427/20000000000000 : ℝ)^3631 := by
    have hnat : (5293525691 : ℕ)^4655*20000000000000^3631 ≤ 8848439894427^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293525691 10000000000 8848439894427 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1674660793/10000000000 : ℝ)^4655 ≤ (10117234786621/100000000000000 : ℝ)^3631 := by
    have hnat : (1674660793 : ℕ)^4655*100000000000000^3631 ≤ 10117234786621^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674660793 10000000000 10117234786621 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355896331/2500000000 : ℝ)^4655 ≤ (1141014143157/2500000000000 : ℝ)^3631 := by
    have hnat : (1355896331 : ℕ)^4655*2500000000000^3631 ≤ 1141014143157^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355896331 2500000000 1141014143157 2500000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293525691/10000000000 : ℝ), (-1674660793/10000000000 : ℝ), (1355896331/2500000000 : ℝ)] ![(8848439894427/20000000000000 : ℝ), (10117234786621/100000000000000 : ℝ), (1141014143157/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293525691/10000000000 : ℝ)|^4655 ≤ (8848439894427/20000000000000 : ℝ)^3631
        have hw : |(5293525691/10000000000 : ℝ)|=(5293525691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1674660793/10000000000 : ℝ)|^4655 ≤ (10117234786621/100000000000000 : ℝ)^3631
        have hw : |(-1674660793/10000000000 : ℝ)|=(1674660793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355896331/2500000000 : ℝ)|^4655 ≤ (1141014143157/2500000000000 : ℝ)^3631
        have hw : |(1355896331/2500000000 : ℝ)|=(1355896331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s5_6 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330845357/625000000 : ℝ)*x 0 + (1355896329/2500000000 : ℝ)*x 1 + (-209332597/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330845357/625000000 : ℝ)^4655 ≤ (22121099848573/50000000000000 : ℝ)^3631 := by
    have hnat : (330845357 : ℕ)^4655*50000000000000^3631 ≤ 22121099848573^3631*625000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330845357 625000000 22121099848573 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355896329/2500000000 : ℝ)^4655 ≤ (11410141409993/25000000000000 : ℝ)^3631 := by
    have hnat : (1355896329 : ℕ)^4655*25000000000000^3631 ≤ 11410141409993^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355896329 2500000000 11410141409993 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209332597/1250000000 : ℝ)^4655 ≤ (5058617327477/50000000000000 : ℝ)^3631 := by
    have hnat : (209332597 : ℕ)^4655*50000000000000^3631 ≤ 5058617327477^3631*1250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209332597 1250000000 5058617327477 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330845357/625000000 : ℝ), (1355896329/2500000000 : ℝ), (-209332597/1250000000 : ℝ)] ![(22121099848573/50000000000000 : ℝ), (11410141409993/25000000000000 : ℝ), (5058617327477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330845357/625000000 : ℝ)|^4655 ≤ (22121099848573/50000000000000 : ℝ)^3631
        have hw : |(330845357/625000000 : ℝ)|=(330845357/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355896329/2500000000 : ℝ)|^4655 ≤ (11410141409993/25000000000000 : ℝ)^3631
        have hw : |(1355896329/2500000000 : ℝ)|=(1355896329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209332597/1250000000 : ℝ)|^4655 ≤ (5058617327477/50000000000000 : ℝ)^3631
        have hw : |(-209332597/1250000000 : ℝ)|=(209332597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s5_7 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239621343/10000000000 : ℝ)*x 0 + (4485230881/10000000000 : ℝ)*x 1 + (400506959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239621343/10000000000 : ℝ)^4655 ≤ (33283374417791/100000000000000 : ℝ)^3631 := by
    have hnat : (4239621343 : ℕ)^4655*100000000000000^3631 ≤ 33283374417791^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239621343 10000000000 33283374417791 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485230881/10000000000 : ℝ)^4655 ≤ (8943810001731/25000000000000 : ℝ)^3631 := by
    have hnat : (4485230881 : ℕ)^4655*25000000000000^3631 ≤ 8943810001731^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485230881 10000000000 8943810001731 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400506959/1000000000 : ℝ)^4655 ≤ (30941385561809/100000000000000 : ℝ)^3631 := by
    have hnat : (400506959 : ℕ)^4655*100000000000000^3631 ≤ 30941385561809^3631*1000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400506959 1000000000 30941385561809 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239621343/10000000000 : ℝ), (4485230881/10000000000 : ℝ), (400506959/1000000000 : ℝ)] ![(33283374417791/100000000000000 : ℝ), (8943810001731/25000000000000 : ℝ), (30941385561809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239621343/10000000000 : ℝ)|^4655 ≤ (33283374417791/100000000000000 : ℝ)^3631
        have hw : |(4239621343/10000000000 : ℝ)|=(4239621343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485230881/10000000000 : ℝ)|^4655 ≤ (8943810001731/25000000000000 : ℝ)^3631
        have hw : |(4485230881/10000000000 : ℝ)|=(4485230881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400506959/1000000000 : ℝ)|^4655 ≤ (30941385561809/100000000000000 : ℝ)^3631
        have hw : |(400506959/1000000000 : ℝ)|=(400506959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1579_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (223/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11147/100000 : ℝ) ^ (4653/1024 : ℝ) ≤ (936198759506927/20000000000000000000 : ℝ) := by
    have hpowers : (11147/100000 : ℝ)^4653 ≤ (936198759506927/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11147 : ℕ)^4653*20000000000000000000^1024 ≤ 936198759506927^1024*100000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11147 100000 936198759506927 20000000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11147/100000 : ℝ)) (X := (936198759506927/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15487/100000 : ℝ) ^ (4653/1024 : ℝ) ≤ (2085718543652417/10000000000000000000 : ℝ) := by
    have hpowers : (15487/100000 : ℝ)^4653 ≤ (2085718543652417/10000000000000000000 : ℝ)^1024 := by
      have hnat : (15487 : ℕ)^4653*10000000000000000000^1024 ≤ 2085718543652417^1024*100000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15487 100000 2085718543652417 10000000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15487/100000 : ℝ)) (X := (2085718543652417/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000936198759506927/10000000000000000000 : ℝ) ≤ (1250025753076841/1250000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (10000936198759506927/10000000000000000000 : ℝ)^1024 ≤ (1250025753076841/1250000000000000 : ℝ)^4653 := by
      have hnat : (10000936198759506927 : ℕ)^1024*1250000000000000^4653 ≤ 1250025753076841^4653*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000936198759506927 10000000000000000000 1250025753076841 1250000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250025753076841/1250000000000000 : ℝ)) (X := (10000936198759506927/10000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005107635846811761/20000000000000000000 : ℝ) ≤ (5000280985295013/5000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (20005107635846811761/20000000000000000000 : ℝ)^1024 ≤ (5000280985295013/5000000000000000 : ℝ)^4653 := by
      have hnat : (20005107635846811761 : ℕ)^1024*5000000000000000^4653 ≤ 5000280985295013^4653*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005107635846811761 20000000000000000000 5000280985295013 5000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000280985295013/5000000000000000 : ℝ)) (X := (20005107635846811761/20000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002085718543652417/5000000000000000000 : ℝ) ≤ (2500229479141331/2500000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (5002085718543652417/5000000000000000000 : ℝ)^1024 ≤ (2500229479141331/2500000000000000 : ℝ)^4653 := by
      have hnat : (5002085718543652417 : ℕ)^1024*2500000000000000^4653 ≤ 2500229479141331^4653*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002085718543652417 5000000000000000000 2500229479141331 2500000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500229479141331/2500000000000000 : ℝ)) (X := (5002085718543652417/5000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(936198759506927/20000000000000000000 : ℝ) ≤ ((10848239671813656477/10850000000000000000 : ℝ)+2*(177972987649/217000000000000 : ℝ)*(11147/100000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (10848239671813656477/10850000000000000000 : ℝ)+2*(177972987649/217000000000000 : ℝ)*(11147/100000 : ℝ)=(1250025753076841/1250000000000000 : ℝ) by norm_num, show 1+2*(936198759506927/20000000000000000000 : ℝ)=(10000936198759506927/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2085718543652417/10000000000000000000 : ℝ)+(936198759506927/20000000000000000000 : ℝ) ≤ ((10848239671813656477/10850000000000000000 : ℝ)+(177972987649/217000000000000 : ℝ)*((15487/100000 : ℝ)+(11147/100000 : ℝ)))^(4653/1024 : ℝ) := by
    rw [show (10848239671813656477/10850000000000000000 : ℝ)+(177972987649/217000000000000 : ℝ)*((15487/100000 : ℝ)+(11147/100000 : ℝ))=(5000280985295013/5000000000000000 : ℝ) by norm_num, show 1+(2085718543652417/10000000000000000000 : ℝ)+(936198759506927/20000000000000000000 : ℝ)=(20005107635846811761/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2085718543652417/10000000000000000000 : ℝ) ≤ ((10848239671813656477/10850000000000000000 : ℝ)+2*(177972987649/217000000000000 : ℝ)*(15487/100000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (10848239671813656477/10850000000000000000 : ℝ)+2*(177972987649/217000000000000 : ℝ)*(15487/100000 : ℝ)=(2500229479141331/2500000000000000 : ℝ) by norm_num, show 1+2*(2085718543652417/10000000000000000000 : ℝ)=(5002085718543652417/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10848239671813656477/10850000000000000000 : ℝ)*(X 1 0+X 2 0)+(177972987649/217000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (10848239671813656477/10850000000000000000 : ℝ)) (alpha := (177972987649/217000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10848239671813656477/10850000000000000000 : ℝ)*(X 0 1+X 2 1)+(177972987649/217000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (10848239671813656477/10850000000000000000 : ℝ)) (alpha := (177972987649/217000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10848239671813656477/10850000000000000000 : ℝ)*(X 0 2+X 1 2)+(177972987649/217000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (10848239671813656477/10850000000000000000 : ℝ)) (alpha := (177972987649/217000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-886695517/5000000000 : ℝ)*X 0 0+(5424660291/10000000000 : ℝ)*X 0 1+(652543591/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347636789/10000000000 : ℝ)*X 1 0+(-1877896629/10000000000 : ℝ)*X 1 1+(5220349379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668454609/1250000000 : ℝ)*X 2 0+(5220349483/10000000000 : ℝ)*X 2 1+(-1877896379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4239558983/10000000000 : ℝ)*X 0 0+(80050367/200000000 : ℝ)*X 0 1+(897552579/2000000000 : ℝ)*X 0 2+(4239558983/10000000000 : ℝ)*X 1 0+(80050367/200000000 : ℝ)*X 1 1+(897552579/2000000000 : ℝ)*X 1 2+(4239558983/10000000000 : ℝ)*X 2 0+(80050367/200000000 : ℝ)*X 2 1+(897552579/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-221677209/1250000000 : ℝ)*X 0 0+(1044283141/2000000000 : ℝ)*X 0 1+(5423585309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293525691/10000000000 : ℝ)*X 1 0+(-1674660793/10000000000 : ℝ)*X 1 1+(1355896331/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330845357/625000000 : ℝ)*X 2 0+(1355896329/2500000000 : ℝ)*X 2 1+(-209332597/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4239621343/10000000000 : ℝ)*X 0 0+(4485230881/10000000000 : ℝ)*X 0 1+(400506959/1000000000 : ℝ)*X 0 2+(4239621343/10000000000 : ℝ)*X 1 0+(4485230881/10000000000 : ℝ)*X 1 1+(400506959/1000000000 : ℝ)*X 1 2+(4239621343/10000000000 : ℝ)*X 2 0+(4485230881/10000000000 : ℝ)*X 2 1+(400506959/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (158278682031058164158477883/27125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1399977231/100000000000000 : ℝ)*(base19) + (1054864597/100000000000000 : ℝ)*(base23) + (225178573/100000000000000 : ℝ)*(lower2) + (29957157/20000000000000 : ℝ)*(upper3) + (112640981/100000000000000 : ℝ)*(upper5) + (173884924290631/5000000000000 : ℝ)*(major0) + (173884924290631/5000000000000 : ℝ)*(major1) + (173884924290631/5000000000000 : ℝ)*(major2) + (4894522621199541/100000000000000 : ℝ)*(sp0) + (1223640613372667/25000000000000 : ℝ)*(sp1) + (2447281399301651/50000000000000 : ℝ)*(sp2) + (2060823724037629/100000000000000 : ℝ)*(sp3) + (20616134179/50000000000000 : ℝ)*(sp4) + (9199614413/100000000000000 : ℝ)*(sp7) + (1030416461826021/50000000000000 : ℝ)*(f.failure) + (4894563853467899/100000000000000 : ℝ)*(f.sum) + (863143793689/542500000000000000000000000 : ℝ)*base65 + (893858610332483013/54250000000000000000000000000000 : ℝ)*base68 + (81865999534233013/54250000000000000000000000000000 : ℝ)*base70 + (168232537856983013/54250000000000000000000000000000 : ℝ)*base72 + (425511646403/1085000000000000000000000000 : ℝ)*base73 + (743076321617733013/54250000000000000000000000000000 : ℝ)*base76 + (179688309197983013/54250000000000000000000000000000 : ℝ)*base78 + (819639404773733013/54250000000000000000000000000000 : ℝ)*base80 + (1254873346843/1085000000000000000000000000 : ℝ)*base81 + (27351743/5000000000000000000000 : ℝ)*base89 + (27351743/5000000000000000000000 : ℝ)*base91 + (27351743/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1813559786478426145265248521/271250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249714727/25000000000000 : ℝ)*(base19) + (561088843/50000000000000 : ℝ)*(base23) + (324406163/100000000000000 : ℝ)*(lower1) + (140132587/100000000000000 : ℝ)*(upper3) + (43517023/100000000000000 : ℝ)*(lower4) + (3244279/2500000000000 : ℝ)*(upper5) + (3514475930296391/100000000000000 : ℝ)*(major0) + (3514475930296391/100000000000000 : ℝ)*(major1) + (3514475930296391/100000000000000 : ℝ)*(major2) + (1051059041/50000000000000 : ℝ)*(sp2) + (4946324941916533/100000000000000 : ℝ)*(sp4) + (39570591544461/800000000000 : ℝ)*(sp5) + (989264343524153/20000000000000 : ℝ)*(sp6) + (65082084244117/3125000000000 : ℝ)*(sp7) + (65082084244117/3125000000000 : ℝ)*(f.failure) + (4946324941916533/100000000000000 : ℝ)*(f.sum) + (13723546748841/10850000000000000000000000000 : ℝ)*base66 + (19665351959660175493/1085000000000000000000000000000000 : ℝ)*base68 + (13935099609040175493/1085000000000000000000000000000000 : ℝ)*base70 + (51379661998890175493/1085000000000000000000000000000000 : ℝ)*base72 + (46520805478391/10850000000000000000000000000 : ℝ)*base74 + (51215589634704824507/1085000000000000000000000000000000 : ℝ)*base75 + (6420284059155175493/1085000000000000000000000000000000 : ℝ)*base78 + (2174053485045175493/1085000000000000000000000000000000 : ℝ)*base80 + (48998472450941/10850000000000000000000000000 : ℝ)*base82 + (2370711/312500000000000000000 : ℝ)*base89 + (2370711/312500000000000000000 : ℝ)*base91 + (2370711/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1579_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1579_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1579_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3947/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1579_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1579_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1579_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3947/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1579_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
