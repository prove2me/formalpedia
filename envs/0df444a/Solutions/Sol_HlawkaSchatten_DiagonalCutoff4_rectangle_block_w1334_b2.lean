-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1334_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:42.636962+00:00
-- url     : https://prove2.me/submissions/bfa794dc-f578-4fe7-aa34-5320c86ec314

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
theorem support_rectangle_w1334_s6_0 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-51272399/250000000 : ℝ)*x 0 + (2706568311/5000000000 : ℝ)*x 1 + (1311086641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51272399/250000000 : ℝ)^2147 ≤ (12487597220619/100000000000000 : ℝ)^1635 := by
    have hnat : (51272399 : ℕ)^2147*100000000000000^1635 ≤ 12487597220619^1635*250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51272399 250000000 12487597220619 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706568311/5000000000 : ℝ)^2147 ≤ (44666156148399/100000000000000 : ℝ)^1635 := by
    have hnat : (2706568311 : ℕ)^2147*100000000000000^1635 ≤ 44666156148399^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706568311 5000000000 44666156148399 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311086641/2500000000 : ℝ)^2147 ≤ (42846246620263/100000000000000 : ℝ)^1635 := by
    have hnat : (1311086641 : ℕ)^2147*100000000000000^1635 ≤ 42846246620263^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311086641 2500000000 42846246620263 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51272399/250000000 : ℝ), (2706568311/5000000000 : ℝ), (1311086641/2500000000 : ℝ)] ![(12487597220619/100000000000000 : ℝ), (44666156148399/100000000000000 : ℝ), (42846246620263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51272399/250000000 : ℝ)|^2147 ≤ (12487597220619/100000000000000 : ℝ)^1635
        have hw : |(-51272399/250000000 : ℝ)|=(51272399/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706568311/5000000000 : ℝ)|^2147 ≤ (44666156148399/100000000000000 : ℝ)^1635
        have hw : |(2706568311/5000000000 : ℝ)|=(2706568311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311086641/2500000000 : ℝ)|^2147 ≤ (42846246620263/100000000000000 : ℝ)^1635
        have hw : |(1311086641/2500000000 : ℝ)|=(1311086641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s6_1 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337284923/2500000000 : ℝ)*x 0 + (-2136902407/10000000000 : ℝ)*x 1 + (5244346567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337284923/2500000000 : ℝ)^2147 ≤ (21987006314671/50000000000000 : ℝ)^1635 := by
    have hnat : (1337284923 : ℕ)^2147*50000000000000^1635 ≤ 21987006314671^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337284923 2500000000 21987006314671 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136902407/10000000000 : ℝ)^2147 ≤ (13179740696491/100000000000000 : ℝ)^1635 := by
    have hnat : (2136902407 : ℕ)^2147*100000000000000^1635 ≤ 13179740696491^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136902407 10000000000 13179740696491 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244346567/10000000000 : ℝ)^2147 ≤ (1338945207889/3125000000000 : ℝ)^1635 := by
    have hnat : (5244346567 : ℕ)^2147*3125000000000^1635 ≤ 1338945207889^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244346567 10000000000 1338945207889 3125000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337284923/2500000000 : ℝ), (-2136902407/10000000000 : ℝ), (5244346567/10000000000 : ℝ)] ![(21987006314671/50000000000000 : ℝ), (13179740696491/100000000000000 : ℝ), (1338945207889/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337284923/2500000000 : ℝ)|^2147 ≤ (21987006314671/50000000000000 : ℝ)^1635
        have hw : |(1337284923/2500000000 : ℝ)|=(1337284923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136902407/10000000000 : ℝ)|^2147 ≤ (13179740696491/100000000000000 : ℝ)^1635
        have hw : |(-2136902407/10000000000 : ℝ)|=(2136902407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244346567/10000000000 : ℝ)|^2147 ≤ (1338945207889/3125000000000 : ℝ)^1635
        have hw : |(5244346567/10000000000 : ℝ)|=(5244346567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s6_2 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674569849/5000000000 : ℝ)*x 0 + (5244346559/10000000000 : ℝ)*x 1 + (-2136902411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674569849/5000000000 : ℝ)^2147 ≤ (1374187896691/3125000000000 : ℝ)^1635 := by
    have hnat : (2674569849 : ℕ)^2147*3125000000000^1635 ≤ 1374187896691^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674569849 5000000000 1374187896691 3125000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244346559/10000000000 : ℝ)^2147 ≤ (42846246566621/100000000000000 : ℝ)^1635 := by
    have hnat : (5244346559 : ℕ)^2147*100000000000000^1635 ≤ 42846246566621^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244346559 10000000000 42846246566621 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136902411/10000000000 : ℝ)^2147 ≤ (1647467591111/12500000000000 : ℝ)^1635 := by
    have hnat : (2136902411 : ℕ)^2147*12500000000000^1635 ≤ 1647467591111^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136902411 10000000000 1647467591111 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674569849/5000000000 : ℝ), (5244346559/10000000000 : ℝ), (-2136902411/10000000000 : ℝ)] ![(1374187896691/3125000000000 : ℝ), (42846246566621/100000000000000 : ℝ), (1647467591111/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674569849/5000000000 : ℝ)|^2147 ≤ (1374187896691/3125000000000 : ℝ)^1635
        have hw : |(2674569849/5000000000 : ℝ)|=(2674569849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244346559/10000000000 : ℝ)|^2147 ≤ (42846246566621/100000000000000 : ℝ)^1635
        have hw : |(5244346559/10000000000 : ℝ)|=(5244346559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2136902411/10000000000 : ℝ)|^2147 ≤ (1647467591111/12500000000000 : ℝ)^1635
        have hw : |(-2136902411/10000000000 : ℝ)|=(2136902411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s6_3 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4328713617/10000000000 : ℝ)*x 0 + (2077919573/5000000000 : ℝ)*x 1 + (180332733/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328713617/10000000000 : ℝ)^2147 ≤ (16651550908717/50000000000000 : ℝ)^1635 := by
    have hnat : (4328713617 : ℕ)^2147*50000000000000^1635 ≤ 16651550908717^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328713617 10000000000 16651550908717 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077919573/5000000000 : ℝ)^2147 ≤ (15783807421043/50000000000000 : ℝ)^1635 := by
    have hnat : (2077919573 : ℕ)^2147*50000000000000^1635 ≤ 15783807421043^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077919573 5000000000 15783807421043 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180332733/400000000 : ℝ)^2147 ≤ (35129283324801/100000000000000 : ℝ)^1635 := by
    have hnat : (180332733 : ℕ)^2147*100000000000000^1635 ≤ 35129283324801^1635*400000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180332733 400000000 35129283324801 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328713617/10000000000 : ℝ), (2077919573/5000000000 : ℝ), (180332733/400000000 : ℝ)] ![(16651550908717/50000000000000 : ℝ), (15783807421043/50000000000000 : ℝ), (35129283324801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328713617/10000000000 : ℝ)|^2147 ≤ (16651550908717/50000000000000 : ℝ)^1635
        have hw : |(4328713617/10000000000 : ℝ)|=(4328713617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077919573/5000000000 : ℝ)|^2147 ≤ (15783807421043/50000000000000 : ℝ)^1635
        have hw : |(2077919573/5000000000 : ℝ)|=(2077919573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180332733/400000000 : ℝ)|^2147 ≤ (35129283324801/100000000000000 : ℝ)^1635
        have hw : |(180332733/400000000 : ℝ)|=(180332733/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s6_4 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2050908257/10000000000 : ℝ)*x 0 + (5244950641/10000000000 : ℝ)*x 1 + (1353132353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050908257/10000000000 : ℝ)^2147 ≤ (624384777113/5000000000000 : ℝ)^1635 := by
    have hnat : (2050908257 : ℕ)^2147*5000000000000^1635 ≤ 624384777113^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050908257 10000000000 624384777113 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244950641/10000000000 : ℝ)^2147 ≤ (42852727527717/100000000000000 : ℝ)^1635 := by
    have hnat : (5244950641 : ℕ)^2147*100000000000000^1635 ≤ 42852727527717^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244950641 10000000000 42852727527717 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353132353/2500000000 : ℝ)^2147 ≤ (22329788458463/50000000000000 : ℝ)^1635 := by
    have hnat : (1353132353 : ℕ)^2147*50000000000000^1635 ≤ 22329788458463^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353132353 2500000000 22329788458463 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2050908257/10000000000 : ℝ), (5244950641/10000000000 : ℝ), (1353132353/2500000000 : ℝ)] ![(624384777113/5000000000000 : ℝ), (42852727527717/100000000000000 : ℝ), (22329788458463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2050908257/10000000000 : ℝ)|^2147 ≤ (624384777113/5000000000000 : ℝ)^1635
        have hw : |(-2050908257/10000000000 : ℝ)|=(2050908257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244950641/10000000000 : ℝ)|^2147 ≤ (42852727527717/100000000000000 : ℝ)^1635
        have hw : |(5244950641/10000000000 : ℝ)|=(5244950641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353132353/2500000000 : ℝ)|^2147 ≤ (22329788458463/50000000000000 : ℝ)^1635
        have hw : |(1353132353/2500000000 : ℝ)|=(1353132353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s6_5 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305703459/10000000000 : ℝ)*x 0 + (-123044977/625000000 : ℝ)*x 1 + (5412529443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305703459/10000000000 : ℝ)^2147 ≤ (43505711674171/100000000000000 : ℝ)^1635 := by
    have hnat : (5305703459 : ℕ)^2147*100000000000000^1635 ≤ 43505711674171^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305703459 10000000000 43505711674171 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123044977/625000000 : ℝ)^2147 ≤ (2958677766973/25000000000000 : ℝ)^1635 := by
    have hnat : (123044977 : ℕ)^2147*25000000000000^1635 ≤ 2958677766973^1635*625000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123044977 625000000 2958677766973 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412529443/10000000000 : ℝ)^2147 ≤ (44659577252811/100000000000000 : ℝ)^1635 := by
    have hnat : (5412529443 : ℕ)^2147*100000000000000^1635 ≤ 44659577252811^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412529443 10000000000 44659577252811 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305703459/10000000000 : ℝ), (-123044977/625000000 : ℝ), (5412529443/10000000000 : ℝ)] ![(43505711674171/100000000000000 : ℝ), (2958677766973/25000000000000 : ℝ), (44659577252811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305703459/10000000000 : ℝ)|^2147 ≤ (43505711674171/100000000000000 : ℝ)^1635
        have hw : |(5305703459/10000000000 : ℝ)|=(5305703459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123044977/625000000 : ℝ)|^2147 ≤ (2958677766973/25000000000000 : ℝ)^1635
        have hw : |(-123044977/625000000 : ℝ)|=(123044977/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412529443/10000000000 : ℝ)|^2147 ≤ (44659577252811/100000000000000 : ℝ)^1635
        have hw : |(5412529443/10000000000 : ℝ)|=(5412529443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s6_6 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652851749/5000000000 : ℝ)*x 0 + (5412529391/10000000000 : ℝ)*x 1 + (-1968719649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652851749/5000000000 : ℝ)^2147 ≤ (21752856047053/50000000000000 : ℝ)^1635 := by
    have hnat : (2652851749 : ℕ)^2147*50000000000000^1635 ≤ 21752856047053^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652851749 5000000000 21752856047053 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412529391/10000000000 : ℝ)^2147 ≤ (44659576689391/100000000000000 : ℝ)^1635 := by
    have hnat : (5412529391 : ℕ)^2147*100000000000000^1635 ≤ 44659576689391^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412529391 10000000000 44659576689391 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1968719649/10000000000 : ℝ)^2147 ≤ (11834711202087/100000000000000 : ℝ)^1635 := by
    have hnat : (1968719649 : ℕ)^2147*100000000000000^1635 ≤ 11834711202087^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968719649 10000000000 11834711202087 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652851749/5000000000 : ℝ), (5412529391/10000000000 : ℝ), (-1968719649/10000000000 : ℝ)] ![(21752856047053/50000000000000 : ℝ), (44659576689391/100000000000000 : ℝ), (11834711202087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652851749/5000000000 : ℝ)|^2147 ≤ (21752856047053/50000000000000 : ℝ)^1635
        have hw : |(2652851749/5000000000 : ℝ)|=(2652851749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412529391/10000000000 : ℝ)|^2147 ≤ (44659576689391/100000000000000 : ℝ)^1635
        have hw : |(5412529391/10000000000 : ℝ)|=(5412529391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1968719649/10000000000 : ℝ)|^2147 ≤ (11834711202087/100000000000000 : ℝ)^1635
        have hw : |(-1968719649/10000000000 : ℝ)|=(1968719649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s6_7 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (173149571/400000000 : ℝ)*x 0 + (225352837/500000000 : ℝ)*x 1 + (2078553601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173149571/400000000 : ℝ)^2147 ≤ (1665168051717/5000000000000 : ℝ)^1635 := by
    have hnat : (173149571 : ℕ)^2147*5000000000000^1635 ≤ 1665168051717^1635*400000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173149571 400000000 1665168051717 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225352837/500000000 : ℝ)^2147 ≤ (35116375100887/100000000000000 : ℝ)^1635 := by
    have hnat : (225352837 : ℕ)^2147*100000000000000^1635 ≤ 35116375100887^1635*500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225352837 500000000 35116375100887 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078553601/5000000000 : ℝ)^2147 ≤ (31580263851237/100000000000000 : ℝ)^1635 := by
    have hnat : (2078553601 : ℕ)^2147*100000000000000^1635 ≤ 31580263851237^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078553601 5000000000 31580263851237 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173149571/400000000 : ℝ), (225352837/500000000 : ℝ), (2078553601/5000000000 : ℝ)] ![(1665168051717/5000000000000 : ℝ), (35116375100887/100000000000000 : ℝ), (31580263851237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173149571/400000000 : ℝ)|^2147 ≤ (1665168051717/5000000000000 : ℝ)^1635
        have hw : |(173149571/400000000 : ℝ)|=(173149571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225352837/500000000 : ℝ)|^2147 ≤ (35116375100887/100000000000000 : ℝ)^1635
        have hw : |(225352837/500000000 : ℝ)|=(225352837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078553601/5000000000 : ℝ)|^2147 ≤ (31580263851237/100000000000000 : ℝ)^1635
        have hw : |(2078553601/5000000000 : ℝ)|=(2078553601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1334_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1113/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14703/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5561/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5561/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5561/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5561/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5561/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5561/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5561/50000 : ℝ) ^ (4293/1024 : ℝ) ≤ (2507110949077079/25000000000000000000 : ℝ) := by
    have hpowers : (5561/50000 : ℝ)^4293 ≤ (2507110949077079/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5561 : ℕ)^4293*25000000000000000000^1024 ≤ 2507110949077079^1024*50000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5561 50000 2507110949077079 25000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5561/50000 : ℝ)) (X := (2507110949077079/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14711/100000 : ℝ) ^ (4293/1024 : ℝ) ≤ (16195988168116259/50000000000000000000 : ℝ) := by
    have hpowers : (14711/100000 : ℝ)^4293 ≤ (16195988168116259/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14711 : ℕ)^4293*50000000000000000000^1024 ≤ 16195988168116259^1024*100000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14711 100000 16195988168116259 50000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14711/100000 : ℝ)) (X := (16195988168116259/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502507110949077079/12500000000000000000 : ℝ) ≤ (2000095675214071/2000000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (12502507110949077079/12500000000000000000 : ℝ)^1024 ≤ (2000095675214071/2000000000000000 : ℝ)^4293 := by
      have hnat : (12502507110949077079 : ℕ)^1024*2000000000000000^4293 ≤ 2000095675214071^4293*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502507110949077079 12500000000000000000 2000095675214071 2000000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000095675214071/2000000000000000 : ℝ)) (X := (12502507110949077079/12500000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021210210066270417/50000000000000000000 : ℝ) ≤ (10001011681719441/10000000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (50021210210066270417/50000000000000000000 : ℝ)^1024 ≤ (10001011681719441/10000000000000000 : ℝ)^4293 := by
      have hnat : (50021210210066270417 : ℕ)^1024*10000000000000000^4293 ≤ 10001011681719441^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021210210066270417 50000000000000000000 10001011681719441 10000000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001011681719441/10000000000000000 : ℝ)) (X := (50021210210066270417/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016195988168116259/25000000000000000000 : ℝ) ≤ (10001544987368527/10000000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (25016195988168116259/25000000000000000000 : ℝ)^1024 ≤ (10001544987368527/10000000000000000 : ℝ)^4293 := by
      have hnat : (25016195988168116259 : ℕ)^1024*10000000000000000^4293 ≤ 10001544987368527^4293*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016195988168116259 25000000000000000000 10001544987368527 10000000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001544987368527/10000000000000000 : ℝ)) (X := (25016195988168116259/25000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2507110949077079/25000000000000000000 : ℝ) ≤ ((35879854040858235111/35890000000000000000 : ℝ)+2*(266652824543/179450000000000 : ℝ)*(5561/50000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (35879854040858235111/35890000000000000000 : ℝ)+2*(266652824543/179450000000000 : ℝ)*(5561/50000 : ℝ)=(2000095675214071/2000000000000000 : ℝ) by norm_num, show 1+2*(2507110949077079/25000000000000000000 : ℝ)=(12502507110949077079/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16195988168116259/50000000000000000000 : ℝ)+(2507110949077079/25000000000000000000 : ℝ) ≤ ((35879854040858235111/35890000000000000000 : ℝ)+(266652824543/179450000000000 : ℝ)*((14711/100000 : ℝ)+(5561/50000 : ℝ)))^(4293/1024 : ℝ) := by
    rw [show (35879854040858235111/35890000000000000000 : ℝ)+(266652824543/179450000000000 : ℝ)*((14711/100000 : ℝ)+(5561/50000 : ℝ))=(10001011681719441/10000000000000000 : ℝ) by norm_num, show 1+(16195988168116259/50000000000000000000 : ℝ)+(2507110949077079/25000000000000000000 : ℝ)=(50021210210066270417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16195988168116259/50000000000000000000 : ℝ) ≤ ((35879854040858235111/35890000000000000000 : ℝ)+2*(266652824543/179450000000000 : ℝ)*(14711/100000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (35879854040858235111/35890000000000000000 : ℝ)+2*(266652824543/179450000000000 : ℝ)*(14711/100000 : ℝ)=(10001544987368527/10000000000000000 : ℝ) by norm_num, show 1+2*(16195988168116259/50000000000000000000 : ℝ)=(25016195988168116259/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35879854040858235111/35890000000000000000 : ℝ)*(X 1 0+X 2 0)+(266652824543/179450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (35879854040858235111/35890000000000000000 : ℝ)) (alpha := (266652824543/179450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35879854040858235111/35890000000000000000 : ℝ)*(X 0 1+X 2 1)+(266652824543/179450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (35879854040858235111/35890000000000000000 : ℝ)) (alpha := (266652824543/179450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35879854040858235111/35890000000000000000 : ℝ)*(X 0 2+X 1 2)+(266652824543/179450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (35879854040858235111/35890000000000000000 : ℝ)) (alpha := (266652824543/179450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51272399/250000000 : ℝ)*X 0 0+(2706568311/5000000000 : ℝ)*X 0 1+(1311086641/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337284923/2500000000 : ℝ)*X 1 0+(-2136902407/10000000000 : ℝ)*X 1 1+(5244346567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674569849/5000000000 : ℝ)*X 2 0+(5244346559/10000000000 : ℝ)*X 2 1+(-2136902411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328713617/10000000000 : ℝ)*X 0 0+(2077919573/5000000000 : ℝ)*X 0 1+(180332733/400000000 : ℝ)*X 0 2+(4328713617/10000000000 : ℝ)*X 1 0+(2077919573/5000000000 : ℝ)*X 1 1+(180332733/400000000 : ℝ)*X 1 2+(4328713617/10000000000 : ℝ)*X 2 0+(2077919573/5000000000 : ℝ)*X 2 1+(180332733/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2050908257/10000000000 : ℝ)*X 0 0+(5244950641/10000000000 : ℝ)*X 0 1+(1353132353/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305703459/10000000000 : ℝ)*X 1 0+(-123044977/625000000 : ℝ)*X 1 1+(5412529443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652851749/5000000000 : ℝ)*X 2 0+(5412529391/10000000000 : ℝ)*X 2 1+(-1968719649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173149571/400000000 : ℝ)*X 0 0+(225352837/500000000 : ℝ)*X 0 1+(2078553601/5000000000 : ℝ)*X 0 2+(173149571/400000000 : ℝ)*X 1 0+(225352837/500000000 : ℝ)*X 1 1+(2078553601/5000000000 : ℝ)*X 1 2+(173149571/400000000 : ℝ)*X 2 0+(225352837/500000000 : ℝ)*X 2 1+(2078553601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1814048070421581878695061223/897250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179573973/50000000000000 : ℝ)*(base19) + (34761181/10000000000000 : ℝ)*(base23) + (4862781/50000000000000 : ℝ)*(lower2) + (21875343/50000000000000 : ℝ)*(upper3) + (68401/250000000000 : ℝ)*(upper5) + (2190397516570777/50000000000000 : ℝ)*(major0) + (2190397516570777/50000000000000 : ℝ)*(major1) + (2190397516570777/50000000000000 : ℝ)*(major2) + (5924527529148083/100000000000000 : ℝ)*(sp0) + (236981393192703/4000000000000 : ℝ)*(sp1) + (5924534841353711/100000000000000 : ℝ)*(sp2) + (709262682543737/25000000000000 : ℝ)*(sp3) + (7659817437/100000000000000 : ℝ)*(sp4) + (254984359/6250000000000 : ℝ)*(sp7) + (709263702481173/25000000000000 : ℝ)*(f.failure) + (74056689862069/1250000000000 : ℝ)*(f.sum) + (13379543962629/17945000000000000000000000000 : ℝ)*base65 + (3997479904269348753/1794500000000000000000000000000000 : ℝ)*base68 + (19006427630737848753/1794500000000000000000000000000000 : ℝ)*base70 + (19562681665891848753/1794500000000000000000000000000000 : ℝ)*base72 + (62810025972509/17945000000000000000000000000 : ℝ)*base73 + (21601850968508348753/1794500000000000000000000000000000 : ℝ)*base76 + (5239040768212848753/1794500000000000000000000000000000 : ℝ)*base78 + (19251102632686348753/1794500000000000000000000000000000 : ℝ)*base80 + (27320285177829/17945000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4930867/2500000000000000000000 : ℝ)*base89 + (4930867/2500000000000000000000 : ℝ)*base91 + (4930867/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103627887225510727091019/8972500000000000000000000000 : ℝ) := by norm_num
    linear_combination (115838831/6250000000000 : ℝ)*(base19) + (2038412979/100000000000000 : ℝ)*(base23) + (113822263/50000000000000 : ℝ)*(upper3) + (68700131/100000000000000 : ℝ)*(lower4) + (128257521/50000000000000 : ℝ)*(upper5) + (4412448690035591/100000000000000 : ℝ)*(major0) + (4412448690035591/100000000000000 : ℝ)*(major1) + (4412448690035591/100000000000000 : ℝ)*(major2) + (19059782309/50000000000000 : ℝ)*(sp1) + (39541987931/100000000000000 : ℝ)*(sp2) + (5967342901616777/100000000000000 : ℝ)*(sp4) + (5967302928630863/100000000000000 : ℝ)*(sp5) + (2983650660607933/50000000000000 : ℝ)*(sp6) + (285755409347107/10000000000000 : ℝ)*(sp7) + (285755409347107/10000000000000 : ℝ)*(f.failure) + (5967342901616777/100000000000000 : ℝ)*(f.sum) + (86088497917319/17945000000000000000000000000 : ℝ)*base66 + (36246911291245435601/3589000000000000000000000000000000 : ℝ)*base67 + (11308686044477564399/3589000000000000000000000000000000 : ℝ)*base70 + (47515794863528564399/3589000000000000000000000000000000 : ℝ)*base72 + (1462466972469/280390625000000000000000000 : ℝ)*base73 + (39856741854423435601/3589000000000000000000000000000000 : ℝ)*base75 + (17161509137665564399/3589000000000000000000000000000000 : ℝ)*base78 + (21613147893203435601/3589000000000000000000000000000000 : ℝ)*base79 + (79589660609599/17945000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (455253/1000000000000000000000 : ℝ)*base89 + (455253/1000000000000000000000 : ℝ)*base91 + (455253/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1334_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1113/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1334_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1334_s7_0 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2050902489/10000000000 : ℝ)*x 0 + (1353267387/2500000000 : ℝ)*x 1 + (32777559/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050902489/10000000000 : ℝ)^2147 ≤ (6243824711867/50000000000000 : ℝ)^1635 := by
    have hnat : (2050902489 : ℕ)^2147*50000000000000^1635 ≤ 6243824711867^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050902489 10000000000 6243824711867 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353267387/2500000000 : ℝ)^2147 ≤ (44665429377979/100000000000000 : ℝ)^1635 := by
    have hnat : (1353267387 : ℕ)^2147*100000000000000^1635 ≤ 44665429377979^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353267387 2500000000 44665429377979 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32777559/62500000 : ℝ)^2147 ≤ (42846921181541/100000000000000 : ℝ)^1635 := by
    have hnat : (32777559 : ℕ)^2147*100000000000000^1635 ≤ 42846921181541^1635*62500000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32777559 62500000 42846921181541 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2050902489/10000000000 : ℝ), (1353267387/2500000000 : ℝ), (32777559/62500000 : ℝ)] ![(6243824711867/50000000000000 : ℝ), (44665429377979/100000000000000 : ℝ), (42846921181541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2050902489/10000000000 : ℝ)|^2147 ≤ (6243824711867/50000000000000 : ℝ)^1635
        have hw : |(-2050902489/10000000000 : ℝ)|=(2050902489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353267387/2500000000 : ℝ)|^2147 ≤ (44665429377979/100000000000000 : ℝ)^1635
        have hw : |(1353267387/2500000000 : ℝ)|=(1353267387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32777559/62500000 : ℝ)|^2147 ≤ (42846921181541/100000000000000 : ℝ)^1635
        have hw : |(32777559/62500000 : ℝ)|=(32777559/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s7_1 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349122927/10000000000 : ℝ)*x 0 + (-2136841481/10000000000 : ℝ)*x 1 + (5244409431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349122927/10000000000 : ℝ)^2147 ≤ (43973831649673/100000000000000 : ℝ)^1635 := by
    have hnat : (5349122927 : ℕ)^2147*100000000000000^1635 ≤ 43973831649673^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349122927 10000000000 43973831649673 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136841481/10000000000 : ℝ)^2147 ≤ (823702953329/6250000000000 : ℝ)^1635 := by
    have hnat : (2136841481 : ℕ)^2147*6250000000000^1635 ≤ 823702953329^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136841481 10000000000 823702953329 6250000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244409431/10000000000 : ℝ)^2147 ≤ (8569384216997/20000000000000 : ℝ)^1635 := by
    have hnat : (5244409431 : ℕ)^2147*20000000000000^1635 ≤ 8569384216997^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244409431 10000000000 8569384216997 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349122927/10000000000 : ℝ), (-2136841481/10000000000 : ℝ), (5244409431/10000000000 : ℝ)] ![(43973831649673/100000000000000 : ℝ), (823702953329/6250000000000 : ℝ), (8569384216997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349122927/10000000000 : ℝ)|^2147 ≤ (43973831649673/100000000000000 : ℝ)^1635
        have hw : |(5349122927/10000000000 : ℝ)|=(5349122927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136841481/10000000000 : ℝ)|^2147 ≤ (823702953329/6250000000000 : ℝ)^1635
        have hw : |(-2136841481/10000000000 : ℝ)|=(2136841481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244409431/10000000000 : ℝ)|^2147 ≤ (8569384216997/20000000000000 : ℝ)^1635
        have hw : |(5244409431/10000000000 : ℝ)|=(5244409431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s7_2 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349122957/10000000000 : ℝ)*x 0 + (1311102347/2500000000 : ℝ)*x 1 + (-1068420749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349122957/10000000000 : ℝ)^2147 ≤ (1758953278941/4000000000000 : ℝ)^1635 := by
    have hnat : (5349122957 : ℕ)^2147*4000000000000^1635 ≤ 1758953278941^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349122957 10000000000 1758953278941 4000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311102347/2500000000 : ℝ)^2147 ≤ (42846920623661/100000000000000 : ℝ)^1635 := by
    have hnat : (1311102347 : ℕ)^2147*100000000000000^1635 ≤ 42846920623661^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311102347 2500000000 42846920623661 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068420749/5000000000 : ℝ)^2147 ≤ (13179247390947/100000000000000 : ℝ)^1635 := by
    have hnat : (1068420749 : ℕ)^2147*100000000000000^1635 ≤ 13179247390947^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068420749 5000000000 13179247390947 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349122957/10000000000 : ℝ), (1311102347/2500000000 : ℝ), (-1068420749/5000000000 : ℝ)] ![(1758953278941/4000000000000 : ℝ), (42846920623661/100000000000000 : ℝ), (13179247390947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349122957/10000000000 : ℝ)|^2147 ≤ (1758953278941/4000000000000 : ℝ)^1635
        have hw : |(5349122957/10000000000 : ℝ)|=(5349122957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311102347/2500000000 : ℝ)|^2147 ≤ (42846920623661/100000000000000 : ℝ)^1635
        have hw : |(1311102347/2500000000 : ℝ)|=(1311102347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1068420749/5000000000 : ℝ)|^2147 ≤ (13179247390947/100000000000000 : ℝ)^1635
        have hw : |(-1068420749/5000000000 : ℝ)|=(1068420749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s7_3 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4328718249/10000000000 : ℝ)*x 0 + (4155974239/10000000000 : ℝ)*x 1 + (2254091029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328718249/10000000000 : ℝ)^2147 ≤ (6660629722687/20000000000000 : ℝ)^1635 := by
    have hnat : (4328718249 : ℕ)^2147*20000000000000^1635 ≤ 6660629722687^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328718249 10000000000 6660629722687 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4155974239/10000000000 : ℝ)^2147 ≤ (15784481176643/50000000000000 : ℝ)^1635 := by
    have hnat : (4155974239 : ℕ)^2147*50000000000000^1635 ≤ 15784481176643^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155974239 10000000000 15784481176643 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254091029/5000000000 : ℝ)^2147 ≤ (7025577804051/20000000000000 : ℝ)^1635 := by
    have hnat : (2254091029 : ℕ)^2147*20000000000000^1635 ≤ 7025577804051^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254091029 5000000000 7025577804051 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328718249/10000000000 : ℝ), (4155974239/10000000000 : ℝ), (2254091029/5000000000 : ℝ)] ![(6660629722687/20000000000000 : ℝ), (15784481176643/50000000000000 : ℝ), (7025577804051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328718249/10000000000 : ℝ)|^2147 ≤ (6660629722687/20000000000000 : ℝ)^1635
        have hw : |(4328718249/10000000000 : ℝ)|=(4328718249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4155974239/10000000000 : ℝ)|^2147 ≤ (15784481176643/50000000000000 : ℝ)^1635
        have hw : |(4155974239/10000000000 : ℝ)|=(4155974239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254091029/5000000000 : ℝ)|^2147 ≤ (7025577804051/20000000000000 : ℝ)^1635
        have hw : |(2254091029/5000000000 : ℝ)|=(2254091029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s7_4 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2050914907/10000000000 : ℝ)*x 0 + (5245012333/10000000000 : ℝ)*x 1 + (676557927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050914907/10000000000 : ℝ)^2147 ≤ (12487748712941/100000000000000 : ℝ)^1635 := by
    have hnat : (2050914907 : ℕ)^2147*100000000000000^1635 ≤ 12487748712941^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050914907 10000000000 12487748712941 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245012333/10000000000 : ℝ)^2147 ≤ (21426694705187/50000000000000 : ℝ)^1635 := by
    have hnat : (5245012333 : ℕ)^2147*50000000000000^1635 ≤ 21426694705187^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245012333 10000000000 21426694705187 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676557927/1250000000 : ℝ)^2147 ≤ (22329430926057/50000000000000 : ℝ)^1635 := by
    have hnat : (676557927 : ℕ)^2147*50000000000000^1635 ≤ 22329430926057^1635*1250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676557927 1250000000 22329430926057 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2050914907/10000000000 : ℝ), (5245012333/10000000000 : ℝ), (676557927/1250000000 : ℝ)] ![(12487748712941/100000000000000 : ℝ), (21426694705187/50000000000000 : ℝ), (22329430926057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2050914907/10000000000 : ℝ)|^2147 ≤ (12487748712941/100000000000000 : ℝ)^1635
        have hw : |(-2050914907/10000000000 : ℝ)|=(2050914907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245012333/10000000000 : ℝ)|^2147 ≤ (21426694705187/50000000000000 : ℝ)^1635
        have hw : |(5245012333/10000000000 : ℝ)|=(5245012333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676557927/1250000000 : ℝ)|^2147 ≤ (22329430926057/50000000000000 : ℝ)^1635
        have hw : |(676557927/1250000000 : ℝ)|=(676557927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s7_5 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061143903/2000000000 : ℝ)*x 0 + (-1968787983/10000000000 : ℝ)*x 1 + (5412463689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061143903/2000000000 : ℝ)^2147 ≤ (5438235569789/12500000000000 : ℝ)^1635 := by
    have hnat : (1061143903 : ℕ)^2147*12500000000000^1635 ≤ 5438235569789^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061143903 2000000000 5438235569789 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1968787983/10000000000 : ℝ)^2147 ≤ (11835250622379/100000000000000 : ℝ)^1635 := by
    have hnat : (1968787983 : ℕ)^2147*100000000000000^1635 ≤ 11835250622379^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968787983 10000000000 11835250622379 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412463689/10000000000 : ℝ)^2147 ≤ (5582358101257/12500000000000 : ℝ)^1635 := by
    have hnat : (5412463689 : ℕ)^2147*12500000000000^1635 ≤ 5582358101257^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412463689 10000000000 5582358101257 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061143903/2000000000 : ℝ), (-1968787983/10000000000 : ℝ), (5412463689/10000000000 : ℝ)] ![(5438235569789/12500000000000 : ℝ), (11835250622379/100000000000000 : ℝ), (5582358101257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061143903/2000000000 : ℝ)|^2147 ≤ (5438235569789/12500000000000 : ℝ)^1635
        have hw : |(1061143903/2000000000 : ℝ)|=(1061143903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1968787983/10000000000 : ℝ)|^2147 ≤ (11835250622379/100000000000000 : ℝ)^1635
        have hw : |(-1968787983/10000000000 : ℝ)|=(1968787983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412463689/10000000000 : ℝ)|^2147 ≤ (5582358101257/12500000000000 : ℝ)^1635
        have hw : |(5412463689/10000000000 : ℝ)|=(5412463689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s7_6 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663215011/1250000000 : ℝ)*x 0 + (1353115821/2500000000 : ℝ)*x 1 + (-492196939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663215011/1250000000 : ℝ)^2147 ≤ (21752945364067/50000000000000 : ℝ)^1635 := by
    have hnat : (663215011 : ℕ)^2147*50000000000000^1635 ≤ 21752945364067^1635*1250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663215011 1250000000 21752945364067 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353115821/2500000000 : ℝ)^2147 ≤ (446588604219/1000000000000 : ℝ)^1635 := by
    have hnat : (1353115821 : ℕ)^2147*1000000000000^1635 ≤ 446588604219^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353115821 2500000000 446588604219 1000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492196939/2500000000 : ℝ)^2147 ≤ (11835248830459/100000000000000 : ℝ)^1635 := by
    have hnat : (492196939 : ℕ)^2147*100000000000000^1635 ≤ 11835248830459^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492196939 2500000000 11835248830459 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663215011/1250000000 : ℝ), (1353115821/2500000000 : ℝ), (-492196939/2500000000 : ℝ)] ![(21752945364067/50000000000000 : ℝ), (446588604219/1000000000000 : ℝ), (11835248830459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663215011/1250000000 : ℝ)|^2147 ≤ (21752945364067/50000000000000 : ℝ)^1635
        have hw : |(663215011/1250000000 : ℝ)|=(663215011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353115821/2500000000 : ℝ)|^2147 ≤ (446588604219/1000000000000 : ℝ)^1635
        have hw : |(1353115821/2500000000 : ℝ)|=(1353115821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492196939/2500000000 : ℝ)|^2147 ≤ (11835248830459/100000000000000 : ℝ)^1635
        have hw : |(-492196939/2500000000 : ℝ)|=(492196939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s7_7 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4328744039/10000000000 : ℝ)*x 0 + (901384547/2000000000 : ℝ)*x 1 + (831447963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328744039/10000000000 : ℝ)^2147 ≤ (6660681832799/20000000000000 : ℝ)^1635 := by
    have hnat : (4328744039 : ℕ)^2147*20000000000000^1635 ≤ 6660681832799^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328744039 10000000000 6660681832799 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901384547/2000000000 : ℝ)^2147 ≤ (35115004061527/100000000000000 : ℝ)^1635 := by
    have hnat : (901384547 : ℕ)^2147*100000000000000^1635 ≤ 35115004061527^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901384547 2000000000 35115004061527 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831447963/2000000000 : ℝ)^2147 ≤ (31581586751451/100000000000000 : ℝ)^1635 := by
    have hnat : (831447963 : ℕ)^2147*100000000000000^1635 ≤ 31581586751451^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831447963 2000000000 31581586751451 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328744039/10000000000 : ℝ), (901384547/2000000000 : ℝ), (831447963/2000000000 : ℝ)] ![(6660681832799/20000000000000 : ℝ), (35115004061527/100000000000000 : ℝ), (31581586751451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328744039/10000000000 : ℝ)|^2147 ≤ (6660681832799/20000000000000 : ℝ)^1635
        have hw : |(4328744039/10000000000 : ℝ)|=(4328744039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901384547/2000000000 : ℝ)|^2147 ≤ (35115004061527/100000000000000 : ℝ)^1635
        have hw : |(901384547/2000000000 : ℝ)|=(901384547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831447963/2000000000 : ℝ)|^2147 ≤ (31581586751451/100000000000000 : ℝ)^1635
        have hw : |(831447963/2000000000 : ℝ)|=(831447963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1334_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11131/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14701/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1113/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1113/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1113/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1113/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1113/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1113/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1113/10000 : ℝ) ^ (4293/1024 : ℝ) ≤ (10058719913419961/100000000000000000000 : ℝ) := by
    have hpowers : (1113/10000 : ℝ)^4293 ≤ (10058719913419961/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1113 : ℕ)^4293*100000000000000000000^1024 ≤ 10058719913419961^1024*10000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1113 10000 10058719913419961 100000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1113/10000 : ℝ)) (X := (10058719913419961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14703/100000 : ℝ) ^ (4293/1024 : ℝ) ≤ (32318191150108739/100000000000000000000 : ℝ) := by
    have hpowers : (14703/100000 : ℝ)^4293 ≤ (32318191150108739/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14703 : ℕ)^4293*100000000000000000000^1024 ≤ 32318191150108739^1024*100000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14703 100000 32318191150108739 100000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14703/100000 : ℝ)) (X := (32318191150108739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010058719913419961/50000000000000000000 : ℝ) ≤ (1000047982018881/1000000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (50010058719913419961/50000000000000000000 : ℝ)^1024 ≤ (1000047982018881/1000000000000000 : ℝ)^4293 := by
      have hnat : (50010058719913419961 : ℕ)^1024*1000000000000000^4293 ≤ 1000047982018881^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010058719913419961 50000000000000000000 1000047982018881 1000000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000047982018881/1000000000000000 : ℝ)) (X := (50010058719913419961/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000423769110635287/1000000000000000000 : ℝ) ≤ (1000101064424197/1000000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (1000423769110635287/1000000000000000000 : ℝ)^1024 ≤ (1000101064424197/1000000000000000 : ℝ)^4293 := by
      have hnat : (1000423769110635287 : ℕ)^1024*1000000000000000^4293 ≤ 1000101064424197^4293*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000423769110635287 1000000000000000000 1000101064424197 1000000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000101064424197/1000000000000000 : ℝ)) (X := (1000423769110635287/1000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032318191150108739/50000000000000000000 : ℝ) ≤ (1000154146829513/1000000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (50032318191150108739/50000000000000000000 : ℝ)^1024 ≤ (1000154146829513/1000000000000000 : ℝ)^4293 := by
      have hnat : (50032318191150108739 : ℕ)^1024*1000000000000000^4293 ≤ 1000154146829513^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032318191150108739 50000000000000000000 1000154146829513 1000000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000154146829513/1000000000000000 : ℝ)) (X := (50032318191150108739/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10058719913419961/100000000000000000000 : ℝ) ≤ ((1190663275137042551/1191000000000000000 : ℝ)+2*(13270601329/8932500000000 : ℝ)*(1113/10000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (1190663275137042551/1191000000000000000 : ℝ)+2*(13270601329/8932500000000 : ℝ)*(1113/10000 : ℝ)=(1000047982018881/1000000000000000 : ℝ) by norm_num, show 1+2*(10058719913419961/100000000000000000000 : ℝ)=(50010058719913419961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32318191150108739/100000000000000000000 : ℝ)+(10058719913419961/100000000000000000000 : ℝ) ≤ ((1190663275137042551/1191000000000000000 : ℝ)+(13270601329/8932500000000 : ℝ)*((14703/100000 : ℝ)+(1113/10000 : ℝ)))^(4293/1024 : ℝ) := by
    rw [show (1190663275137042551/1191000000000000000 : ℝ)+(13270601329/8932500000000 : ℝ)*((14703/100000 : ℝ)+(1113/10000 : ℝ))=(1000101064424197/1000000000000000 : ℝ) by norm_num, show 1+(32318191150108739/100000000000000000000 : ℝ)+(10058719913419961/100000000000000000000 : ℝ)=(1000423769110635287/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32318191150108739/100000000000000000000 : ℝ) ≤ ((1190663275137042551/1191000000000000000 : ℝ)+2*(13270601329/8932500000000 : ℝ)*(14703/100000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (1190663275137042551/1191000000000000000 : ℝ)+2*(13270601329/8932500000000 : ℝ)*(14703/100000 : ℝ)=(1000154146829513/1000000000000000 : ℝ) by norm_num, show 1+2*(32318191150108739/100000000000000000000 : ℝ)=(50032318191150108739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1190663275137042551/1191000000000000000 : ℝ)*(X 1 0+X 2 0)+(13270601329/8932500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (1113/10000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (1190663275137042551/1191000000000000000 : ℝ)) (alpha := (13270601329/8932500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1190663275137042551/1191000000000000000 : ℝ)*(X 0 1+X 2 1)+(13270601329/8932500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (1113/10000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (1190663275137042551/1191000000000000000 : ℝ)) (alpha := (13270601329/8932500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1190663275137042551/1191000000000000000 : ℝ)*(X 0 2+X 1 2)+(13270601329/8932500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (1113/10000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (1190663275137042551/1191000000000000000 : ℝ)) (alpha := (13270601329/8932500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2050902489/10000000000 : ℝ)*X 0 0+(1353267387/2500000000 : ℝ)*X 0 1+(32777559/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349122927/10000000000 : ℝ)*X 1 0+(-2136841481/10000000000 : ℝ)*X 1 1+(5244409431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349122957/10000000000 : ℝ)*X 2 0+(1311102347/2500000000 : ℝ)*X 2 1+(-1068420749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328718249/10000000000 : ℝ)*X 0 0+(4155974239/10000000000 : ℝ)*X 0 1+(2254091029/5000000000 : ℝ)*X 0 2+(4328718249/10000000000 : ℝ)*X 1 0+(4155974239/10000000000 : ℝ)*X 1 1+(2254091029/5000000000 : ℝ)*X 1 2+(4328718249/10000000000 : ℝ)*X 2 0+(4155974239/10000000000 : ℝ)*X 2 1+(2254091029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2050914907/10000000000 : ℝ)*X 0 0+(5245012333/10000000000 : ℝ)*X 0 1+(676557927/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061143903/2000000000 : ℝ)*X 1 0+(-1968787983/10000000000 : ℝ)*X 1 1+(5412463689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663215011/1250000000 : ℝ)*X 2 0+(1353115821/2500000000 : ℝ)*X 2 1+(-492196939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328744039/10000000000 : ℝ)*X 0 0+(901384547/2000000000 : ℝ)*X 0 1+(831447963/2000000000 : ℝ)*X 0 2+(4328744039/10000000000 : ℝ)*X 1 0+(901384547/2000000000 : ℝ)*X 1 1+(831447963/2000000000 : ℝ)*X 1 2+(4328744039/10000000000 : ℝ)*X 2 0+(901384547/2000000000 : ℝ)*X 2 1+(831447963/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9471138168091084138522393/1860937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (201203181/20000000000000 : ℝ)*(base19) + (985052117/100000000000000 : ℝ)*(base23) + (29001161/100000000000000 : ℝ)*(lower2) + (34073011/25000000000000 : ℝ)*(upper3) + (10178693/12500000000000 : ℝ)*(upper5) + (274011828683831/6250000000000 : ℝ)*(major0) + (274011828683831/6250000000000 : ℝ)*(major1) + (274011828683831/6250000000000 : ℝ)*(major2) + (5929105356746493/100000000000000 : ℝ)*(sp0) + (592912439141797/10000000000000 : ℝ)*(sp1) + (5929124412381757/100000000000000 : ℝ)*(sp2) + (709810569042487/25000000000000 : ℝ)*(sp3) + (20040687381/100000000000000 : ℝ)*(sp4) + (667164413/6250000000000 : ℝ)*(sp7) + (567850590160111/20000000000000 : ℝ)*(f.failure) + (2964562698716937/50000000000000 : ℝ)*(f.sum) + (89991913979/27914062500000000000000000 : ℝ)*base65 + (6597286338947393/22331250000000000000000000000000 : ℝ)*base67 + (387850534348321357/22331250000000000000000000000000 : ℝ)*base70 + (327351315551333857/22331250000000000000000000000000 : ℝ)*base72 + (4496941931843/1786500000000000000000000000 : ℝ)*base73 + (177924003146708857/22331250000000000000000000000000 : ℝ)*base76 + (239140583716377607/22331250000000000000000000000000 : ℝ)*base78 + (151824390305221357/22331250000000000000000000000000 : ℝ)*base80 + (8831544372871/1786500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13463831/2000000000000000000000 : ℝ)*base90 + (13463831/2000000000000000000000 : ℝ)*base92 + (13463831/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4040607700562821185818317/620312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (120103963/50000000000000 : ℝ)*(base19) + (976740889/100000000000000 : ℝ)*(base23) + (3489031/6250000000000 : ℝ)*(lower1) + (195133/10000000000000 : ℝ)*(upper2) + (217404519/100000000000000 : ℝ)*(upper3) + (117560021/50000000000000 : ℝ)*(upper5) + (275988458009967/6250000000000 : ℝ)*(major0) + (275988458009967/6250000000000 : ℝ)*(major1) + (275988458009967/6250000000000 : ℝ)*(major2) + (10746481539/100000000000000 : ℝ)*(sp2) + (5971896070950479/100000000000000 : ℝ)*(sp4) + (5971895830742553/100000000000000 : ℝ)*(sp5) + (5971884347728051/100000000000000 : ℝ)*(sp6) + (1429867184120459/50000000000000 : ℝ)*(sp7) + (1429867184120459/50000000000000 : ℝ)*(f.failure) + (5971896070950479/100000000000000 : ℝ)*(f.sum) + (1269187973891/1191000000000000000000000000 : ℝ)*base66 + (69573279275662933/7443750000000000000000000000000 : ℝ)*base68 + (376230688520418317/7443750000000000000000000000000 : ℝ)*base69 + (19368024274162933/7443750000000000000000000000000 : ℝ)*base72 + (1934801182747/1191000000000000000000000000 : ℝ)*base73 + (71023172528475433/7443750000000000000000000000000 : ℝ)*base76 + (50634435533887933/7443750000000000000000000000000 : ℝ)*base78 + (73796938274531683/7443750000000000000000000000000 : ℝ)*base80 + (5066774106137/148875000000000000000000000 : ℝ)*base81 + (29266861/5000000000000000000000 : ℝ)*base89 + (29266861/5000000000000000000000 : ℝ)*base91 + (29266861/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1334_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1334_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1334_box_0 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1883012011/10000000000 : ℝ)*x 0 + (2695137051/5000000000 : ℝ)*x 1 + (2695137043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1883012011/10000000000 : ℝ)^2147 ≤ (11162807777673/100000000000000 : ℝ)^1635 := by
    have hnat : (1883012011 : ℕ)^2147*100000000000000^1635 ≤ 11162807777673^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883012011 10000000000 11162807777673 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695137051/5000000000 : ℝ)^2147 ≤ (8883719237461/20000000000000 : ℝ)^1635 := by
    have hnat : (2695137051 : ℕ)^2147*20000000000000^1635 ≤ 8883719237461^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695137051 5000000000 8883719237461 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695137043/5000000000 : ℝ)^2147 ≤ (5552324501771/12500000000000 : ℝ)^1635 := by
    have hnat : (2695137043 : ℕ)^2147*12500000000000^1635 ≤ 5552324501771^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695137043 5000000000 5552324501771 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1883012011/10000000000 : ℝ), (2695137051/5000000000 : ℝ), (2695137043/5000000000 : ℝ)] ![(11162807777673/100000000000000 : ℝ), (8883719237461/20000000000000 : ℝ), (5552324501771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1883012011/10000000000 : ℝ)|^2147 ≤ (11162807777673/100000000000000 : ℝ)^1635
        have hw : |(-1883012011/10000000000 : ℝ)|=(1883012011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695137051/5000000000 : ℝ)|^2147 ≤ (8883719237461/20000000000000 : ℝ)^1635
        have hw : |(2695137051/5000000000 : ℝ)|=(2695137051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695137043/5000000000 : ℝ)|^2147 ≤ (5552324501771/12500000000000 : ℝ)^1635
        have hw : |(2695137043/5000000000 : ℝ)|=(2695137043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_1 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642526021/5000000000 : ℝ)*x 0 + (-253391257/1250000000 : ℝ)*x 1 + (5390274203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642526021/5000000000 : ℝ)^2147 ≤ (21641740896153/50000000000000 : ℝ)^1635 := by
    have hnat : (2642526021 : ℕ)^2147*50000000000000^1635 ≤ 21641740896153^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642526021 5000000000 21641740896153 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253391257/1250000000 : ℝ)^2147 ≤ (12297920918287/100000000000000 : ℝ)^1635 := by
    have hnat : (253391257 : ℕ)^2147*100000000000000^1635 ≤ 12297920918287^1635*1250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253391257 1250000000 12297920918287 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390274203/10000000000 : ℝ)^2147 ≤ (11104649320057/25000000000000 : ℝ)^1635 := by
    have hnat : (5390274203 : ℕ)^2147*25000000000000^1635 ≤ 11104649320057^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390274203 10000000000 11104649320057 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642526021/5000000000 : ℝ), (-253391257/1250000000 : ℝ), (5390274203/10000000000 : ℝ)] ![(21641740896153/50000000000000 : ℝ), (12297920918287/100000000000000 : ℝ), (11104649320057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642526021/5000000000 : ℝ)|^2147 ≤ (21641740896153/50000000000000 : ℝ)^1635
        have hw : |(2642526021/5000000000 : ℝ)|=(2642526021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253391257/1250000000 : ℝ)|^2147 ≤ (12297920918287/100000000000000 : ℝ)^1635
        have hw : |(-253391257/1250000000 : ℝ)|=(253391257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390274203/10000000000 : ℝ)|^2147 ≤ (11104649320057/25000000000000 : ℝ)^1635
        have hw : |(5390274203/10000000000 : ℝ)|=(5390274203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_2 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642525931/5000000000 : ℝ)*x 0 + (5390274239/10000000000 : ℝ)*x 1 + (-8108521/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642525931/5000000000 : ℝ)^2147 ≤ (43283479856509/100000000000000 : ℝ)^1635 := by
    have hnat : (2642525931 : ℕ)^2147*100000000000000^1635 ≤ 43283479856509^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642525931 5000000000 43283479856509 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390274239/10000000000 : ℝ)^2147 ≤ (8883719533957/20000000000000 : ℝ)^1635 := by
    have hnat : (5390274239 : ℕ)^2147*20000000000000^1635 ≤ 8883719533957^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390274239 10000000000 8883719533957 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8108521/40000000 : ℝ)^2147 ≤ (12297922463777/100000000000000 : ℝ)^1635 := by
    have hnat : (8108521 : ℕ)^2147*100000000000000^1635 ≤ 12297922463777^1635*40000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8108521 40000000 12297922463777 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642525931/5000000000 : ℝ), (5390274239/10000000000 : ℝ), (-8108521/40000000 : ℝ)] ![(43283479856509/100000000000000 : ℝ), (8883719533957/20000000000000 : ℝ), (12297922463777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642525931/5000000000 : ℝ)|^2147 ≤ (43283479856509/100000000000000 : ℝ)^1635
        have hw : |(2642525931/5000000000 : ℝ)|=(2642525931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390274239/10000000000 : ℝ)|^2147 ≤ (8883719533957/20000000000000 : ℝ)^1635
        have hw : |(5390274239/10000000000 : ℝ)|=(5390274239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8108521/40000000 : ℝ)|^2147 ≤ (12297922463777/100000000000000 : ℝ)^1635
        have hw : |(-8108521/40000000 : ℝ)|=(8108521/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_3 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4477096951/10000000000 : ℝ)*x 0 + (2129217969/5000000000 : ℝ)*x 1 + (4258436289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4477096951/10000000000 : ℝ)^2147 ≤ (1740508347343/5000000000000 : ℝ)^1635 := by
    have hnat : (4477096951 : ℕ)^2147*5000000000000^1635 ≤ 1740508347343^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477096951 10000000000 1740508347343 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2129217969/5000000000 : ℝ)^2147 ≤ (32594914752043/100000000000000 : ℝ)^1635 := by
    have hnat : (2129217969 : ℕ)^2147*100000000000000^1635 ≤ 32594914752043^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129217969 5000000000 32594914752043 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4258436289/10000000000 : ℝ)^2147 ≤ (16297459139991/50000000000000 : ℝ)^1635 := by
    have hnat : (4258436289 : ℕ)^2147*50000000000000^1635 ≤ 16297459139991^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258436289 10000000000 16297459139991 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4477096951/10000000000 : ℝ), (2129217969/5000000000 : ℝ), (4258436289/10000000000 : ℝ)] ![(1740508347343/5000000000000 : ℝ), (32594914752043/100000000000000 : ℝ), (16297459139991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4477096951/10000000000 : ℝ)|^2147 ≤ (1740508347343/5000000000000 : ℝ)^1635
        have hw : |(4477096951/10000000000 : ℝ)|=(4477096951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2129217969/5000000000 : ℝ)|^2147 ≤ (32594914752043/100000000000000 : ℝ)^1635
        have hw : |(2129217969/5000000000 : ℝ)|=(2129217969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4258436289/10000000000 : ℝ)|^2147 ≤ (16297459139991/50000000000000 : ℝ)^1635
        have hw : |(4258436289/10000000000 : ℝ)|=(4258436289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_4 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2221551213/10000000000 : ℝ)*x 0 + (5264746497/10000000000 : ℝ)*x 1 + (2632372723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221551213/10000000000 : ℝ)^2147 ≤ (554781346353/4000000000000 : ℝ)^1635 := by
    have hnat : (2221551213 : ℕ)^2147*4000000000000^1635 ≤ 554781346353^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221551213 10000000000 554781346353 4000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264746497/10000000000 : ℝ)^2147 ≤ (43065238808727/100000000000000 : ℝ)^1635 := by
    have hnat : (5264746497 : ℕ)^2147*100000000000000^1635 ≤ 43065238808727^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264746497 10000000000 43065238808727 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632372723/5000000000 : ℝ)^2147 ≤ (43065227519443/100000000000000 : ℝ)^1635 := by
    have hnat : (2632372723 : ℕ)^2147*100000000000000^1635 ≤ 43065227519443^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632372723 5000000000 43065227519443 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2221551213/10000000000 : ℝ), (5264746497/10000000000 : ℝ), (2632372723/5000000000 : ℝ)] ![(554781346353/4000000000000 : ℝ), (43065238808727/100000000000000 : ℝ), (43065227519443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2221551213/10000000000 : ℝ)|^2147 ≤ (554781346353/4000000000000 : ℝ)^1635
        have hw : |(-2221551213/10000000000 : ℝ)|=(2221551213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264746497/10000000000 : ℝ)|^2147 ≤ (43065238808727/100000000000000 : ℝ)^1635
        have hw : |(5264746497/10000000000 : ℝ)|=(5264746497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632372723/5000000000 : ℝ)|^2147 ≤ (43065227519443/100000000000000 : ℝ)^1635
        have hw : |(2632372723/5000000000 : ℝ)|=(2632372723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_5 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5373250003/10000000000 : ℝ)*x 0 + (-2077444009/10000000000 : ℝ)*x 1 + (5264746399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373250003/10000000000 : ℝ)^2147 ≤ (44234469207107/100000000000000 : ℝ)^1635 := by
    have hnat : (5373250003 : ℕ)^2147*100000000000000^1635 ≤ 44234469207107^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373250003 10000000000 44234469207107 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077444009/10000000000 : ℝ)^2147 ≤ (12700293013333/100000000000000 : ℝ)^1635 := by
    have hnat : (2077444009 : ℕ)^2147*100000000000000^1635 ≤ 12700293013333^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077444009 10000000000 12700293013333 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264746399/10000000000 : ℝ)^2147 ≤ (43065237756063/100000000000000 : ℝ)^1635 := by
    have hnat : (5264746399 : ℕ)^2147*100000000000000^1635 ≤ 43065237756063^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264746399 10000000000 43065237756063 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373250003/10000000000 : ℝ), (-2077444009/10000000000 : ℝ), (5264746399/10000000000 : ℝ)] ![(44234469207107/100000000000000 : ℝ), (12700293013333/100000000000000 : ℝ), (43065237756063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373250003/10000000000 : ℝ)|^2147 ≤ (44234469207107/100000000000000 : ℝ)^1635
        have hw : |(5373250003/10000000000 : ℝ)|=(5373250003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077444009/10000000000 : ℝ)|^2147 ≤ (12700293013333/100000000000000 : ℝ)^1635
        have hw : |(-2077444009/10000000000 : ℝ)|=(2077444009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264746399/10000000000 : ℝ)|^2147 ≤ (43065237756063/100000000000000 : ℝ)^1635
        have hw : |(5264746399/10000000000 : ℝ)|=(5264746399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_6 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67165631/125000000 : ℝ)*x 0 + (5264746343/10000000000 : ℝ)*x 1 + (-2077443443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67165631/125000000 : ℝ)^2147 ≤ (5529309295453/12500000000000 : ℝ)^1635 := by
    have hnat : (67165631 : ℕ)^2147*12500000000000^1635 ≤ 5529309295453^1635*125000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67165631 125000000 5529309295453 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264746343/10000000000 : ℝ)^2147 ≤ (43065237154541/100000000000000 : ℝ)^1635 := by
    have hnat : (5264746343 : ℕ)^2147*100000000000000^1635 ≤ 43065237154541^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264746343 10000000000 43065237154541 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077443443/10000000000 : ℝ)^2147 ≤ (1587536058697/12500000000000 : ℝ)^1635 := by
    have hnat : (2077443443 : ℕ)^2147*12500000000000^1635 ≤ 1587536058697^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077443443 10000000000 1587536058697 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67165631/125000000 : ℝ), (5264746343/10000000000 : ℝ), (-2077443443/10000000000 : ℝ)] ![(5529309295453/12500000000000 : ℝ), (43065237154541/100000000000000 : ℝ), (1587536058697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67165631/125000000 : ℝ)|^2147 ≤ (5529309295453/12500000000000 : ℝ)^1635
        have hw : |(67165631/125000000 : ℝ)|=(67165631/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264746343/10000000000 : ℝ)|^2147 ≤ (43065237154541/100000000000000 : ℝ)^1635
        have hw : |(5264746343/10000000000 : ℝ)|=(5264746343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077443443/10000000000 : ℝ)|^2147 ≤ (1587536058697/12500000000000 : ℝ)^1635
        have hw : |(-2077443443/10000000000 : ℝ)|=(2077443443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_7 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2089712417/5000000000 : ℝ)*x 0 + (55090223/125000000 : ℝ)*x 1 + (2203609379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089712417/5000000000 : ℝ)^2147 ≤ (795077060603/2500000000000 : ℝ)^1635 := by
    have hnat : (2089712417 : ℕ)^2147*2500000000000^1635 ≤ 795077060603^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089712417 5000000000 795077060603 2500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55090223/125000000 : ℝ)^2147 ≤ (6819690824151/20000000000000 : ℝ)^1635 := by
    have hnat : (55090223 : ℕ)^2147*20000000000000^1635 ≤ 6819690824151^1635*125000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55090223 125000000 6819690824151 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203609379/5000000000 : ℝ)^2147 ≤ (34098463447437/100000000000000 : ℝ)^1635 := by
    have hnat : (2203609379 : ℕ)^2147*100000000000000^1635 ≤ 34098463447437^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203609379 5000000000 34098463447437 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089712417/5000000000 : ℝ), (55090223/125000000 : ℝ), (2203609379/5000000000 : ℝ)] ![(795077060603/2500000000000 : ℝ), (6819690824151/20000000000000 : ℝ), (34098463447437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089712417/5000000000 : ℝ)|^2147 ≤ (795077060603/2500000000000 : ℝ)^1635
        have hw : |(2089712417/5000000000 : ℝ)|=(2089712417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55090223/125000000 : ℝ)|^2147 ≤ (6819690824151/20000000000000 : ℝ)^1635
        have hw : |(55090223/125000000 : ℝ)|=(55090223/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203609379/5000000000 : ℝ)|^2147 ≤ (34098463447437/100000000000000 : ℝ)^1635
        have hw : |(2203609379/5000000000 : ℝ)|=(2203609379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_8 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1075239989/5000000000 : ℝ)*x 0 + (5178366481/10000000000 : ℝ)*x 1 + (216171883/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075239989/5000000000 : ℝ)^2147 ≤ (13289815968263/100000000000000 : ℝ)^1635 := by
    have hnat : (1075239989 : ℕ)^2147*100000000000000^1635 ≤ 13289815968263^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075239989 5000000000 13289815968263 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178366481/10000000000 : ℝ)^2147 ≤ (42139783162221/100000000000000 : ℝ)^1635 := by
    have hnat : (5178366481 : ℕ)^2147*100000000000000^1635 ≤ 42139783162221^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178366481 10000000000 42139783162221 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216171883/400000000 : ℝ)^2147 ≤ (44570400855203/100000000000000 : ℝ)^1635 := by
    have hnat : (216171883 : ℕ)^2147*100000000000000^1635 ≤ 44570400855203^1635*400000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216171883 400000000 44570400855203 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1075239989/5000000000 : ℝ), (5178366481/10000000000 : ℝ), (216171883/400000000 : ℝ)] ![(13289815968263/100000000000000 : ℝ), (42139783162221/100000000000000 : ℝ), (44570400855203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1075239989/5000000000 : ℝ)|^2147 ≤ (13289815968263/100000000000000 : ℝ)^1635
        have hw : |(-1075239989/5000000000 : ℝ)|=(1075239989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178366481/10000000000 : ℝ)|^2147 ≤ (42139783162221/100000000000000 : ℝ)^1635
        have hw : |(5178366481/10000000000 : ℝ)|=(5178366481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216171883/400000000 : ℝ)|^2147 ≤ (44570400855203/100000000000000 : ℝ)^1635
        have hw : |(216171883/400000000 : ℝ)|=(216171883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_9 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275193963/10000000000 : ℝ)*x 0 + (-2021376521/10000000000 : ℝ)*x 1 + (337768557/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275193963/10000000000 : ℝ)^2147 ≤ (21588747397129/50000000000000 : ℝ)^1635 := by
    have hnat : (5275193963 : ℕ)^2147*50000000000000^1635 ≤ 21588747397129^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275193963 10000000000 21588747397129 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2021376521/10000000000 : ℝ)^2147 ≤ (6126053050427/50000000000000 : ℝ)^1635 := by
    have hnat : (2021376521 : ℕ)^2147*50000000000000^1635 ≤ 6126053050427^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021376521 10000000000 6126053050427 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337768557/625000000 : ℝ)^2147 ≤ (2228519954497/5000000000000 : ℝ)^1635 := by
    have hnat : (337768557 : ℕ)^2147*5000000000000^1635 ≤ 2228519954497^1635*625000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337768557 625000000 2228519954497 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275193963/10000000000 : ℝ), (-2021376521/10000000000 : ℝ), (337768557/625000000 : ℝ)] ![(21588747397129/50000000000000 : ℝ), (6126053050427/50000000000000 : ℝ), (2228519954497/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275193963/10000000000 : ℝ)|^2147 ≤ (21588747397129/50000000000000 : ℝ)^1635
        have hw : |(5275193963/10000000000 : ℝ)|=(5275193963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2021376521/10000000000 : ℝ)|^2147 ≤ (6126053050427/50000000000000 : ℝ)^1635
        have hw : |(-2021376521/10000000000 : ℝ)|=(2021376521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337768557/625000000 : ℝ)|^2147 ≤ (2228519954497/5000000000000 : ℝ)^1635
        have hw : |(337768557/625000000 : ℝ)|=(337768557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_10 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2637596821/5000000000 : ℝ)*x 0 + (5404297257/10000000000 : ℝ)*x 1 + (-404275297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637596821/5000000000 : ℝ)^2147 ≤ (8635498268821/20000000000000 : ℝ)^1635 := by
    have hnat : (2637596821 : ℕ)^2147*20000000000000^1635 ≤ 8635498268821^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637596821 5000000000 8635498268821 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404297257/10000000000 : ℝ)^2147 ≤ (5571300353279/12500000000000 : ℝ)^1635 := by
    have hnat : (5404297257 : ℕ)^2147*12500000000000^1635 ≤ 5571300353279^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404297257 10000000000 5571300353279 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404275297/2000000000 : ℝ)^2147 ≤ (6126052907159/50000000000000 : ℝ)^1635 := by
    have hnat : (404275297 : ℕ)^2147*50000000000000^1635 ≤ 6126052907159^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404275297 2000000000 6126052907159 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637596821/5000000000 : ℝ), (5404297257/10000000000 : ℝ), (-404275297/2000000000 : ℝ)] ![(8635498268821/20000000000000 : ℝ), (5571300353279/12500000000000 : ℝ), (6126052907159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637596821/5000000000 : ℝ)|^2147 ≤ (8635498268821/20000000000000 : ℝ)^1635
        have hw : |(2637596821/5000000000 : ℝ)|=(2637596821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404297257/10000000000 : ℝ)|^2147 ≤ (5571300353279/12500000000000 : ℝ)^1635
        have hw : |(5404297257/10000000000 : ℝ)|=(5404297257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404275297/2000000000 : ℝ)|^2147 ≤ (6126052907159/50000000000000 : ℝ)^1635
        have hw : |(-404275297/2000000000 : ℝ)|=(404275297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_11 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2254895757/5000000000 : ℝ)*x 0 + (2120900619/5000000000 : ℝ)*x 1 + (530225181/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254895757/5000000000 : ℝ)^2147 ≤ (8786089514977/25000000000000 : ℝ)^1635 := by
    have hnat : (2254895757 : ℕ)^2147*25000000000000^1635 ≤ 8786089514977^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254895757 5000000000 8786089514977 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120900619/5000000000 : ℝ)^2147 ≤ (32427819909357/100000000000000 : ℝ)^1635 := by
    have hnat : (2120900619 : ℕ)^2147*100000000000000^1635 ≤ 32427819909357^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120900619 5000000000 32427819909357 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530225181/1250000000 : ℝ)^2147 ≤ (6485564403501/20000000000000 : ℝ)^1635 := by
    have hnat : (530225181 : ℕ)^2147*20000000000000^1635 ≤ 6485564403501^1635*1250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530225181 1250000000 6485564403501 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2254895757/5000000000 : ℝ), (2120900619/5000000000 : ℝ), (530225181/1250000000 : ℝ)] ![(8786089514977/25000000000000 : ℝ), (32427819909357/100000000000000 : ℝ), (6485564403501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2254895757/5000000000 : ℝ)|^2147 ≤ (8786089514977/25000000000000 : ℝ)^1635
        have hw : |(2254895757/5000000000 : ℝ)|=(2254895757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120900619/5000000000 : ℝ)|^2147 ≤ (32427819909357/100000000000000 : ℝ)^1635
        have hw : |(2120900619/5000000000 : ℝ)|=(2120900619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530225181/1250000000 : ℝ)|^2147 ≤ (6485564403501/20000000000000 : ℝ)^1635
        have hw : |(530225181/1250000000 : ℝ)|=(530225181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_12 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-977218161/5000000000 : ℝ)*x 0 + (5474430049/10000000000 : ℝ)*x 1 + (1050736661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977218161/5000000000 : ℝ)^2147 ≤ (11722089261803/100000000000000 : ℝ)^1635 := by
    have hnat : (977218161 : ℕ)^2147*100000000000000^1635 ≤ 11722089261803^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977218161 5000000000 11722089261803 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474430049/10000000000 : ℝ)^2147 ≤ (5666433466307/12500000000000 : ℝ)^1635 := by
    have hnat : (5474430049 : ℕ)^2147*12500000000000^1635 ≤ 5666433466307^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474430049 10000000000 5666433466307 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050736661/2000000000 : ℝ)^2147 ≤ (10736610747999/25000000000000 : ℝ)^1635 := by
    have hnat : (1050736661 : ℕ)^2147*25000000000000^1635 ≤ 10736610747999^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050736661 2000000000 10736610747999 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977218161/5000000000 : ℝ), (5474430049/10000000000 : ℝ), (1050736661/2000000000 : ℝ)] ![(11722089261803/100000000000000 : ℝ), (5666433466307/12500000000000 : ℝ), (10736610747999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977218161/5000000000 : ℝ)|^2147 ≤ (11722089261803/100000000000000 : ℝ)^1635
        have hw : |(-977218161/5000000000 : ℝ)|=(977218161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474430049/10000000000 : ℝ)|^2147 ≤ (5666433466307/12500000000000 : ℝ)^1635
        have hw : |(5474430049/10000000000 : ℝ)|=(5474430049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050736661/2000000000 : ℝ)|^2147 ≤ (10736610747999/25000000000000 : ℝ)^1635
        have hw : |(1050736661/2000000000 : ℝ)|=(1050736661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_13 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (215240831/400000000 : ℝ)*x 0 + (-52044343/250000000 : ℝ)*x 1 + (1313420867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215240831/400000000 : ℝ)^2147 ≤ (2769905791241/6250000000000 : ℝ)^1635 := by
    have hnat : (215240831 : ℕ)^2147*6250000000000^1635 ≤ 2769905791241^1635*400000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215240831 400000000 2769905791241 6250000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52044343/250000000 : ℝ)^2147 ≤ (6367531288501/50000000000000 : ℝ)^1635 := by
    have hnat : (52044343 : ℕ)^2147*50000000000000^1635 ≤ 6367531288501^1635*250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52044343 250000000 6367531288501 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313420867/2500000000 : ℝ)^2147 ≤ (42946444741703/100000000000000 : ℝ)^1635 := by
    have hnat : (1313420867 : ℕ)^2147*100000000000000^1635 ≤ 42946444741703^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313420867 2500000000 42946444741703 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215240831/400000000 : ℝ), (-52044343/250000000 : ℝ), (1313420867/2500000000 : ℝ)] ![(2769905791241/6250000000000 : ℝ), (6367531288501/50000000000000 : ℝ), (42946444741703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215240831/400000000 : ℝ)|^2147 ≤ (2769905791241/6250000000000 : ℝ)^1635
        have hw : |(215240831/400000000 : ℝ)|=(215240831/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52044343/250000000 : ℝ)|^2147 ≤ (6367531288501/50000000000000 : ℝ)^1635
        have hw : |(-52044343/250000000 : ℝ)|=(52044343/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313420867/2500000000 : ℝ)|^2147 ≤ (42946444741703/100000000000000 : ℝ)^1635
        have hw : |(1313420867/2500000000 : ℝ)|=(1313420867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_14 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (672627589/1250000000 : ℝ)*x 0 + (1050736663/2000000000 : ℝ)*x 1 + (-208177401/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672627589/1250000000 : ℝ)^2147 ≤ (22159245989249/50000000000000 : ℝ)^1635 := by
    have hnat : (672627589 : ℕ)^2147*50000000000000^1635 ≤ 22159245989249^1635*1250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672627589 1250000000 22159245989249 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050736663/2000000000 : ℝ)^2147 ≤ (2147322154967/5000000000000 : ℝ)^1635 := by
    have hnat : (1050736663 : ℕ)^2147*5000000000000^1635 ≤ 2147322154967^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050736663 2000000000 2147322154967 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208177401/1000000000 : ℝ)^2147 ≤ (6367532453297/50000000000000 : ℝ)^1635 := by
    have hnat : (208177401 : ℕ)^2147*50000000000000^1635 ≤ 6367532453297^1635*1000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208177401 1000000000 6367532453297 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672627589/1250000000 : ℝ), (1050736663/2000000000 : ℝ), (-208177401/1000000000 : ℝ)] ![(22159245989249/50000000000000 : ℝ), (2147322154967/5000000000000 : ℝ), (6367532453297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672627589/1250000000 : ℝ)|^2147 ≤ (22159245989249/50000000000000 : ℝ)^1635
        have hw : |(672627589/1250000000 : ℝ)|=(672627589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050736663/2000000000 : ℝ)|^2147 ≤ (2147322154967/5000000000000 : ℝ)^1635
        have hw : |(1050736663/2000000000 : ℝ)|=(1050736663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208177401/1000000000 : ℝ)|^2147 ≤ (6367532453297/50000000000000 : ℝ)^1635
        have hw : |(-208177401/1000000000 : ℝ)|=(208177401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_box_15 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2076372133/5000000000 : ℝ)*x 0 + (4420319483/10000000000 : ℝ)*x 1 + (442031949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076372133/5000000000 : ℝ)^2147 ≤ (1576837406077/5000000000000 : ℝ)^1635 := by
    have hnat : (2076372133 : ℕ)^2147*5000000000000^1635 ≤ 1576837406077^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076372133 5000000000 1576837406077 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4420319483/10000000000 : ℝ)^2147 ≤ (4278953236829/12500000000000 : ℝ)^1635 := by
    have hnat : (4420319483 : ℕ)^2147*12500000000000^1635 ≤ 4278953236829^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420319483 10000000000 4278953236829 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442031949/1000000000 : ℝ)^2147 ≤ (34231625965817/100000000000000 : ℝ)^1635 := by
    have hnat : (442031949 : ℕ)^2147*100000000000000^1635 ≤ 34231625965817^1635*1000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442031949 1000000000 34231625965817 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2076372133/5000000000 : ℝ), (4420319483/10000000000 : ℝ), (442031949/1000000000 : ℝ)] ![(1576837406077/5000000000000 : ℝ), (4278953236829/12500000000000 : ℝ), (34231625965817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2076372133/5000000000 : ℝ)|^2147 ≤ (1576837406077/5000000000000 : ℝ)^1635
        have hw : |(2076372133/5000000000 : ℝ)|=(2076372133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4420319483/10000000000 : ℝ)|^2147 ≤ (4278953236829/12500000000000 : ℝ)^1635
        have hw : |(4420319483/10000000000 : ℝ)|=(4420319483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442031949/1000000000 : ℝ)|^2147 ≤ (34231625965817/100000000000000 : ℝ)^1635
        have hw : |(442031949/1000000000 : ℝ)|=(442031949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1334_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15713/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29463/50000 : ℝ) ∧ (79907/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84321/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11131/100000 : ℝ) ^ (4293/1024 : ℝ) ≤ (10062509316171317/100000000000000000000 : ℝ) := by
    have hpowers : (11131/100000 : ℝ)^4293 ≤ (10062509316171317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11131 : ℕ)^4293*100000000000000000000^1024 ≤ 10062509316171317^1024*100000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11131 100000 10062509316171317 100000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11131/100000 : ℝ)) (X := (10062509316171317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14701/100000 : ℝ) ^ (4293/1024 : ℝ) ≤ (32299764867884301/100000000000000000000 : ℝ) := by
    have hpowers : (14701/100000 : ℝ)^4293 ≤ (32299764867884301/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14701 : ℕ)^4293*100000000000000000000^1024 ≤ 32299764867884301^1024*100000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14701 100000 32299764867884301 100000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14701/100000 : ℝ)) (X := (32299764867884301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010062509316171317/50000000000000000000 : ℝ) ≤ (400019200037469/400000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (50010062509316171317/50000000000000000000 : ℝ)^1024 ≤ (400019200037469/400000000000000 : ℝ)^4293 := by
      have hnat : (50010062509316171317 : ℕ)^1024*400000000000000^4293 ≤ 400019200037469^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010062509316171317 50000000000000000000 400019200037469 400000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400019200037469/400000000000000 : ℝ)) (X := (50010062509316171317/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021181137092027809/50000000000000000000 : ℝ) ≤ (40004041180897/40000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (50021181137092027809/50000000000000000000 : ℝ)^1024 ≤ (40004041180897/40000000000000 : ℝ)^4293 := by
      have hnat : (50021181137092027809 : ℕ)^1024*40000000000000^4293 ≤ 40004041180897^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021181137092027809 50000000000000000000 40004041180897 40000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40004041180897/40000000000000 : ℝ)) (X := (50021181137092027809/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032299764867884301/50000000000000000000 : ℝ) ≤ (400061623580471/400000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (50032299764867884301/50000000000000000000 : ℝ)^1024 ≤ (400061623580471/400000000000000 : ℝ)^4293 := by
      have hnat : (50032299764867884301 : ℕ)^1024*400000000000000^4293 ≤ 400061623580471^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032299764867884301 50000000000000000000 400061623580471 400000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400061623580471/400000000000000 : ℝ)) (X := (50032299764867884301/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10062509316171317/100000000000000000000 : ℝ) ≤ ((356899081919152267/357000000000000000 : ℝ)+2*(21211771501/14280000000000 : ℝ)*(11131/100000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (356899081919152267/357000000000000000 : ℝ)+2*(21211771501/14280000000000 : ℝ)*(11131/100000 : ℝ)=(400019200037469/400000000000000 : ℝ) by norm_num, show 1+2*(10062509316171317/100000000000000000000 : ℝ)=(50010062509316171317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32299764867884301/100000000000000000000 : ℝ)+(10062509316171317/100000000000000000000 : ℝ) ≤ ((356899081919152267/357000000000000000 : ℝ)+(21211771501/14280000000000 : ℝ)*((14701/100000 : ℝ)+(11131/100000 : ℝ)))^(4293/1024 : ℝ) := by
    rw [show (356899081919152267/357000000000000000 : ℝ)+(21211771501/14280000000000 : ℝ)*((14701/100000 : ℝ)+(11131/100000 : ℝ))=(40004041180897/40000000000000 : ℝ) by norm_num, show 1+(32299764867884301/100000000000000000000 : ℝ)+(10062509316171317/100000000000000000000 : ℝ)=(50021181137092027809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32299764867884301/100000000000000000000 : ℝ) ≤ ((356899081919152267/357000000000000000 : ℝ)+2*(21211771501/14280000000000 : ℝ)*(14701/100000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (356899081919152267/357000000000000000 : ℝ)+2*(21211771501/14280000000000 : ℝ)*(14701/100000 : ℝ)=(400061623580471/400000000000000 : ℝ) by norm_num, show 1+2*(32299764867884301/100000000000000000000 : ℝ)=(50032299764867884301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (356899081919152267/357000000000000000 : ℝ)*(X 1 0+X 2 0)+(21211771501/14280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (356899081919152267/357000000000000000 : ℝ)) (alpha := (21211771501/14280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (356899081919152267/357000000000000000 : ℝ)*(X 0 1+X 2 1)+(21211771501/14280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (356899081919152267/357000000000000000 : ℝ)) (alpha := (21211771501/14280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (356899081919152267/357000000000000000 : ℝ)*(X 0 2+X 1 2)+(21211771501/14280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (356899081919152267/357000000000000000 : ℝ)) (alpha := (21211771501/14280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1883012011/10000000000 : ℝ)*X 0 0+(2695137051/5000000000 : ℝ)*X 0 1+(2695137043/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642526021/5000000000 : ℝ)*X 1 0+(-253391257/1250000000 : ℝ)*X 1 1+(5390274203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642525931/5000000000 : ℝ)*X 2 0+(5390274239/10000000000 : ℝ)*X 2 1+(-8108521/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4477096951/10000000000 : ℝ)*X 0 0+(2129217969/5000000000 : ℝ)*X 0 1+(4258436289/10000000000 : ℝ)*X 0 2+(4477096951/10000000000 : ℝ)*X 1 0+(2129217969/5000000000 : ℝ)*X 1 1+(4258436289/10000000000 : ℝ)*X 1 2+(4477096951/10000000000 : ℝ)*X 2 0+(2129217969/5000000000 : ℝ)*X 2 1+(4258436289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2221551213/10000000000 : ℝ)*X 0 0+(5264746497/10000000000 : ℝ)*X 0 1+(2632372723/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373250003/10000000000 : ℝ)*X 1 0+(-2077444009/10000000000 : ℝ)*X 1 1+(5264746399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((67165631/125000000 : ℝ)*X 2 0+(5264746343/10000000000 : ℝ)*X 2 1+(-2077443443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2089712417/5000000000 : ℝ)*X 0 0+(55090223/125000000 : ℝ)*X 0 1+(2203609379/5000000000 : ℝ)*X 0 2+(2089712417/5000000000 : ℝ)*X 1 0+(55090223/125000000 : ℝ)*X 1 1+(2203609379/5000000000 : ℝ)*X 1 2+(2089712417/5000000000 : ℝ)*X 2 0+(55090223/125000000 : ℝ)*X 2 1+(2203609379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1075239989/5000000000 : ℝ)*X 0 0+(5178366481/10000000000 : ℝ)*X 0 1+(216171883/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275193963/10000000000 : ℝ)*X 1 0+(-2021376521/10000000000 : ℝ)*X 1 1+(337768557/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637596821/5000000000 : ℝ)*X 2 0+(5404297257/10000000000 : ℝ)*X 2 1+(-404275297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2254895757/5000000000 : ℝ)*X 0 0+(2120900619/5000000000 : ℝ)*X 0 1+(530225181/1250000000 : ℝ)*X 0 2+(2254895757/5000000000 : ℝ)*X 1 0+(2120900619/5000000000 : ℝ)*X 1 1+(530225181/1250000000 : ℝ)*X 1 2+(2254895757/5000000000 : ℝ)*X 2 0+(2120900619/5000000000 : ℝ)*X 2 1+(530225181/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-977218161/5000000000 : ℝ)*X 0 0+(5474430049/10000000000 : ℝ)*X 0 1+(1050736661/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((215240831/400000000 : ℝ)*X 1 0+(-52044343/250000000 : ℝ)*X 1 1+(1313420867/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672627589/1250000000 : ℝ)*X 2 0+(1050736663/2000000000 : ℝ)*X 2 1+(-208177401/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2076372133/5000000000 : ℝ)*X 0 0+(4420319483/10000000000 : ℝ)*X 0 1+(442031949/1000000000 : ℝ)*X 0 2+(2076372133/5000000000 : ℝ)*X 1 0+(4420319483/10000000000 : ℝ)*X 1 1+(442031949/1000000000 : ℝ)*X 1 2+(2076372133/5000000000 : ℝ)*X 2 0+(4420319483/10000000000 : ℝ)*X 2 1+(442031949/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15713/25000 : ℝ) ≤ (-373955999020083871941046603419/595000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (196395269/100000000000000 : ℝ)*(upper0) + (67158701/50000000000000 : ℝ)*(lower1) + (308036317/100000000000000 : ℝ)*(lower2) + (291165725117343/10000000000000 : ℝ)*(major0) + (291165725117343/10000000000000 : ℝ)*(major1) + (291165725117343/10000000000000 : ℝ)*(major2) + (9929604689/100000000000000 : ℝ)*(sp3) + (79172567712489/2000000000000 : ℝ)*(sp4) + (247410990513707/6250000000000 : ℝ)*(sp5) + (3958422425957771/100000000000000 : ℝ)*(sp6) + (942806916009379/50000000000000 : ℝ)*(sp7) + (2454202089/20000000000000 : ℝ)*(sp8) + (64808415583/100000000000000 : ℝ)*(sp13) + (218230677123/100000000000000 : ℝ)*(sp14) + (942811880811723/50000000000000 : ℝ)*(f.failure) + (1979320328317447/50000000000000 : ℝ)*(f.sum) + (2214821409/29750000000000000000000000 : ℝ)*base65 + (1874467215750527/1190000000000000000000000000000 : ℝ)*base67 + (3075365229219473/1190000000000000000000000000000 : ℝ)*base70 + (6254580429499473/1190000000000000000000000000000 : ℝ)*base72 + (3120963459759/119000000000000000000000000 : ℝ)*base73 + (1746416375049473/1190000000000000000000000000000 : ℝ)*base76 + (8706507865450527/1190000000000000000000000000000 : ℝ)*base77 + (10879998602819473/1190000000000000000000000000000 : ℝ)*base80 + (201876808933/119000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7585683/5000000000000000000000 : ℝ)*base90 + (7585683/5000000000000000000000 : ℝ)*base92 + (7585683/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29463/50000 : ℝ) ≤ (701245063420027100829110416257/1190000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12640051/100000000000000 : ℝ)*(lower1) + (98511171/100000000000000 : ℝ)*(upper2) + (13479021/100000000000000 : ℝ)*(lower4) + (596016240871343/20000000000000 : ℝ)*(major0) + (596016240871343/20000000000000 : ℝ)*(major1) + (596016240871343/20000000000000 : ℝ)*(major2) + (2005290131376453/50000000000000 : ℝ)*(sp0) + (50132215286779/1250000000000 : ℝ)*(sp1) + (1002645433874399/25000000000000 : ℝ)*(sp2) + (482483888743733/25000000000000 : ℝ)*(sp3) + (408865457/6250000000000 : ℝ)*(sp5) + (507323009/25000000000000 : ℝ)*(sp6) + (46260693/12500000000000 : ℝ)*(sp7) + (140081469/4000000000000 : ℝ)*(sp12) + (482483981265119/25000000000000 : ℝ)*(f.failure) + (31332685662419/781250000000 : ℝ)*(f.sum) + (2367450414247/714000000000000000000000000 : ℝ)*base65 + (111403440923039581/7140000000000000000000000000000 : ℝ)*base67 + (99403167039119581/7140000000000000000000000000000 : ℝ)*base69 + (93937642245299581/7140000000000000000000000000000 : ℝ)*base71 + (1487991741343/714000000000000000000000000 : ℝ)*base73 + (99043093933139581/7140000000000000000000000000000 : ℝ)*base75 + (84371886821459581/7140000000000000000000000000000 : ℝ)*base77 + (79297260998339581/7140000000000000000000000000000 : ℝ)*base79 + (4705236254287/714000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (28860999/2500000000000000000000 : ℝ)*base90 + (28860999/2500000000000000000000 : ℝ)*base92 + (28860999/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79907/100000 : ℝ) ≤ (84904323842172291046891133921/106250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4609703/100000000000000 : ℝ)*(upper0) + (34524789/50000000000000 : ℝ)*(upper2) + (13479129/100000000000000 : ℝ)*(lower3) + (823133123403959/25000000000000 : ℝ)*(major0) + (823133123403959/25000000000000 : ℝ)*(major1) + (823133123403959/25000000000000 : ℝ)*(major2) + (967767/62500000000 : ℝ)*(sp0) + (9259998791/12500000000000 : ℝ)*(sp2) + (460820811/1000000000000 : ℝ)*(sp3) + (1106534988049161/25000000000000 : ℝ)*(sp8) + (8644814944637/195312500000 : ℝ)*(sp9) + (553258896457977/12500000000000 : ℝ)*(sp10) + (266529625359909/12500000000000 : ℝ)*(sp11) + (37510303/1000000000000 : ℝ)*(sp12) + (533070771240093/25000000000000 : ℝ)*(f.failure) + (8644814944637/195312500000 : ℝ)*(f.sum) + (701340964193/178500000000000000000000000 : ℝ)*base65 + (19775574661899947/8925000000000000000000000000000 : ℝ)*base68 + (62498990235800053/8925000000000000000000000000000 : ℝ)*base69 + (36627773006600053/8925000000000000000000000000000 : ℝ)*base71 + (241456556567/178500000000000000000000000 : ℝ)*base73 + (5017471258400053/8925000000000000000000000000000 : ℝ)*base75 + (68130203277800053/8925000000000000000000000000000 : ℝ)*base77 + (72237924496100053/8925000000000000000000000000000 : ℝ)*base79 + (433330225673/178500000000000000000000000 : ℝ)*base81 + (4413547/2500000000000000000000 : ℝ)*base89 + (4413547/2500000000000000000000 : ℝ)*base91 + (4413547/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84321/100000 : ℝ) ≤ (-6271173698572773186108761/7437500000000000000000000 : ℝ) := by norm_num
    linear_combination (24445163/50000000000000 : ℝ)*(lower0) + (27091213/100000000000000 : ℝ)*(upper3) + (31302207/25000000000000 : ℝ)*(lower4) + (1664456235842749/50000000000000 : ℝ)*(major0) + (1664456235842749/50000000000000 : ℝ)*(major1) + (1664456235842749/50000000000000 : ℝ)*(major2) + (1554052267/100000000000000 : ℝ)*(sp4) + (124409764607/100000000000000 : ℝ)*(sp6) + (745880901/1250000000000 : ℝ)*(sp7) + (2989773367/100000000000000 : ℝ)*(sp8) + (2265041655005743/50000000000000 : ℝ)*(sp12) + (4530087853837119/100000000000000 : ℝ)*(sp13) + (4529963444072513/100000000000000 : ℝ)*(sp14) + (2155783519671637/100000000000000 : ℝ)*(sp15) + (2155843190143717/100000000000000 : ℝ)*(f.failure) + (4530087853837119/100000000000000 : ℝ)*(f.sum) + (2802723413603/89250000000000000000000000 : ℝ)*base66 + (93368886006263017/17850000000000000000000000000000 : ℝ)*base68 + (47738457470136983/17850000000000000000000000000000 : ℝ)*base69 + (111375228647136983/17850000000000000000000000000000 : ℝ)*base71 + (49200628969/178500000000000000000000000 : ℝ)*base74 + (23223627058386983/17850000000000000000000000000000 : ℝ)*base75 + (183640706882213017/17850000000000000000000000000000 : ℝ)*base78 + (193262658150863017/17850000000000000000000000000000 : ℝ)*base80 + (1107234014213/178500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (51961443/10000000000000000000000 : ℝ)*base89 + (51961443/10000000000000000000000 : ℝ)*base91 + (51961443/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1334_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29463/50000 : ℝ) else (79907/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84321/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1334_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1334_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29463/50000 : ℝ) else (79907/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84321/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1334_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1334_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1334_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29463/50000 : ℝ) else (79907/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84321/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1334_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
