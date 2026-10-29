-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1513_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:44.699251+00:00
-- url     : https://prove2.me/submissions/c5b91425-9b0a-4d23-bd1d-0a455331201a

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
theorem support_rectangle_w1513_s3_0 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-933024193/5000000000 : ℝ)*x 0 + (2718171409/5000000000 : ℝ)*x 1 + (651846617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933024193/5000000000 : ℝ)^4523 ≤ (11417073839889/100000000000000 : ℝ)^3499 := by
    have hnat : (933024193 : ℕ)^4523*100000000000000^3499 ≤ 11417073839889^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933024193 5000000000 11417073839889 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718171409/5000000000 : ℝ)^4523 ≤ (4548236571923/10000000000000 : ℝ)^3499 := by
    have hnat : (2718171409 : ℕ)^4523*10000000000000^3499 ≤ 4548236571923^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718171409 5000000000 4548236571923 10000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651846617/1250000000 : ℝ)^4523 ≤ (43100560428331/100000000000000 : ℝ)^3499 := by
    have hnat : (651846617 : ℕ)^4523*100000000000000^3499 ≤ 43100560428331^3499*1250000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651846617 1250000000 43100560428331 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933024193/5000000000 : ℝ), (2718171409/5000000000 : ℝ), (651846617/1250000000 : ℝ)] ![(11417073839889/100000000000000 : ℝ), (4548236571923/10000000000000 : ℝ), (43100560428331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933024193/5000000000 : ℝ)|^4523 ≤ (11417073839889/100000000000000 : ℝ)^3499
        have hw : |(-933024193/5000000000 : ℝ)|=(933024193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718171409/5000000000 : ℝ)|^4523 ≤ (4548236571923/10000000000000 : ℝ)^3499
        have hw : |(2718171409/5000000000 : ℝ)|=(2718171409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651846617/1250000000 : ℝ)|^4523 ≤ (43100560428331/100000000000000 : ℝ)^3499
        have hw : |(651846617/1250000000 : ℝ)|=(651846617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s3_1 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107047659/200000000 : ℝ)*x 0 + (-989799909/5000000000 : ℝ)*x 1 + (5214773117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107047659/200000000 : ℝ)^4523 ≤ (44576415321207/100000000000000 : ℝ)^3499 := by
    have hnat : (107047659 : ℕ)^4523*100000000000000^3499 ≤ 44576415321207^3499*200000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107047659 200000000 44576415321207 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989799909/5000000000 : ℝ)^4523 ≤ (1540377788147/12500000000000 : ℝ)^3499 := by
    have hnat : (989799909 : ℕ)^4523*12500000000000^3499 ≤ 1540377788147^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989799909 5000000000 1540377788147 12500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214773117/10000000000 : ℝ)^4523 ≤ (43100562362119/100000000000000 : ℝ)^3499 := by
    have hnat : (5214773117 : ℕ)^4523*100000000000000^3499 ≤ 43100562362119^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214773117 10000000000 43100562362119 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107047659/200000000 : ℝ), (-989799909/5000000000 : ℝ), (5214773117/10000000000 : ℝ)] ![(44576415321207/100000000000000 : ℝ), (1540377788147/12500000000000 : ℝ), (43100562362119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107047659/200000000 : ℝ)|^4523 ≤ (44576415321207/100000000000000 : ℝ)^3499
        have hw : |(107047659/200000000 : ℝ)|=(107047659/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-989799909/5000000000 : ℝ)|^4523 ≤ (1540377788147/12500000000000 : ℝ)^3499
        have hw : |(-989799909/5000000000 : ℝ)|=(989799909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214773117/10000000000 : ℝ)|^4523 ≤ (43100562362119/100000000000000 : ℝ)^3499
        have hw : |(5214773117/10000000000 : ℝ)|=(5214773117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s3_2 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83630987/156250000 : ℝ)*x 0 + (208590919/400000000 : ℝ)*x 1 + (-494899929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83630987/156250000 : ℝ)^4523 ≤ (1114410441703/2500000000000 : ℝ)^3499 := by
    have hnat : (83630987 : ℕ)^4523*2500000000000^3499 ≤ 1114410441703^3499*156250000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83630987 156250000 1114410441703 2500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208590919/400000000 : ℝ)^4523 ≤ (10775140211251/25000000000000 : ℝ)^3499 := by
    have hnat : (208590919 : ℕ)^4523*25000000000000^3499 ≤ 10775140211251^3499*400000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208590919 400000000 10775140211251 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494899929/2500000000 : ℝ)^4523 ≤ (3080755371101/25000000000000 : ℝ)^3499 := by
    have hnat : (494899929 : ℕ)^4523*25000000000000^3499 ≤ 3080755371101^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494899929 2500000000 3080755371101 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83630987/156250000 : ℝ), (208590919/400000000 : ℝ), (-494899929/2500000000 : ℝ)] ![(1114410441703/2500000000000 : ℝ), (10775140211251/25000000000000 : ℝ), (3080755371101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83630987/156250000 : ℝ)|^4523 ≤ (1114410441703/2500000000000 : ℝ)^3499
        have hw : |(83630987/156250000 : ℝ)|=(83630987/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208590919/400000000 : ℝ)|^4523 ≤ (10775140211251/25000000000000 : ℝ)^3499
        have hw : |(208590919/400000000 : ℝ)|=(208590919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494899929/2500000000 : ℝ)|^4523 ≤ (3080755371101/25000000000000 : ℝ)^3499
        have hw : |(-494899929/2500000000 : ℝ)|=(494899929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s3_3 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268998783/10000000000 : ℝ)*x 0 + (1005971309/2500000000 : ℝ)*x 1 + (4526668489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268998783/10000000000 : ℝ)^4523 ≤ (2079788136427/6250000000000 : ℝ)^3499 := by
    have hnat : (4268998783 : ℕ)^4523*6250000000000^3499 ≤ 2079788136427^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268998783 10000000000 2079788136427 6250000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005971309/2500000000 : ℝ)^4523 ≤ (30827841843743/100000000000000 : ℝ)^3499 := by
    have hnat : (1005971309 : ℕ)^4523*100000000000000^3499 ≤ 30827841843743^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005971309 2500000000 30827841843743 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526668489/10000000000 : ℝ)^4523 ≤ (35895547956163/100000000000000 : ℝ)^3499 := by
    have hnat : (4526668489 : ℕ)^4523*100000000000000^3499 ≤ 35895547956163^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526668489 10000000000 35895547956163 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268998783/10000000000 : ℝ), (1005971309/2500000000 : ℝ), (4526668489/10000000000 : ℝ)] ![(2079788136427/6250000000000 : ℝ), (30827841843743/100000000000000 : ℝ), (35895547956163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268998783/10000000000 : ℝ)|^4523 ≤ (2079788136427/6250000000000 : ℝ)^3499
        have hw : |(4268998783/10000000000 : ℝ)|=(4268998783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005971309/2500000000 : ℝ)|^4523 ≤ (30827841843743/100000000000000 : ℝ)^3499
        have hw : |(1005971309/2500000000 : ℝ)|=(1005971309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526668489/10000000000 : ℝ)|^4523 ≤ (35895547956163/100000000000000 : ℝ)^3499
        have hw : |(4526668489/10000000000 : ℝ)|=(4526668489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s3_4 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46651981/250000000 : ℝ)*x 0 + (5215946209/10000000000 : ℝ)*x 1 + (5435161107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46651981/250000000 : ℝ)^4523 ≤ (570865893041/5000000000000 : ℝ)^3499 := by
    have hnat : (46651981 : ℕ)^4523*5000000000000^3499 ≤ 570865893041^3499*250000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46651981 250000000 570865893041 5000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215946209/10000000000 : ℝ)^4523 ≤ (21556547991181/50000000000000 : ℝ)^3499 := by
    have hnat : (5215946209 : ℕ)^4523*50000000000000^3499 ≤ 21556547991181^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215946209 10000000000 21556547991181 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435161107/10000000000 : ℝ)^4523 ≤ (45469586146941/100000000000000 : ℝ)^3499 := by
    have hnat : (5435161107 : ℕ)^4523*100000000000000^3499 ≤ 45469586146941^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435161107 10000000000 45469586146941 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46651981/250000000 : ℝ), (5215946209/10000000000 : ℝ), (5435161107/10000000000 : ℝ)] ![(570865893041/5000000000000 : ℝ), (21556547991181/50000000000000 : ℝ), (45469586146941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46651981/250000000 : ℝ)|^4523 ≤ (570865893041/5000000000000 : ℝ)^3499
        have hw : |(-46651981/250000000 : ℝ)|=(46651981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215946209/10000000000 : ℝ)|^4523 ≤ (21556547991181/50000000000000 : ℝ)^3499
        have hw : |(5215946209/10000000000 : ℝ)|=(5215946209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435161107/10000000000 : ℝ)|^4523 ≤ (45469586146941/100000000000000 : ℝ)^3499
        have hw : |(5435161107/10000000000 : ℝ)|=(5435161107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s3_5 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058841573/2000000000 : ℝ)*x 0 + (-1759211379/10000000000 : ℝ)*x 1 + (1087032269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058841573/2000000000 : ℝ)^4523 ≤ (43951120853631/100000000000000 : ℝ)^3499 := by
    have hnat : (1058841573 : ℕ)^4523*100000000000000^3499 ≤ 43951120853631^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058841573 2000000000 43951120853631 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1759211379/10000000000 : ℝ)^4523 ≤ (2644822601113/25000000000000 : ℝ)^3499 := by
    have hnat : (1759211379 : ℕ)^4523*25000000000000^3499 ≤ 2644822601113^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759211379 10000000000 2644822601113 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087032269/2000000000 : ℝ)^4523 ≤ (22734794360351/50000000000000 : ℝ)^3499 := by
    have hnat : (1087032269 : ℕ)^4523*50000000000000^3499 ≤ 22734794360351^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087032269 2000000000 22734794360351 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058841573/2000000000 : ℝ), (-1759211379/10000000000 : ℝ), (1087032269/2000000000 : ℝ)] ![(43951120853631/100000000000000 : ℝ), (2644822601113/25000000000000 : ℝ), (22734794360351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058841573/2000000000 : ℝ)|^4523 ≤ (43951120853631/100000000000000 : ℝ)^3499
        have hw : |(1058841573/2000000000 : ℝ)|=(1058841573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1759211379/10000000000 : ℝ)|^4523 ≤ (2644822601113/25000000000000 : ℝ)^3499
        have hw : |(-1759211379/10000000000 : ℝ)|=(1759211379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087032269/2000000000 : ℝ)|^4523 ≤ (22734794360351/50000000000000 : ℝ)^3499
        have hw : |(1087032269/2000000000 : ℝ)|=(1087032269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s3_6 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132355203/250000000 : ℝ)*x 0 + (2717580501/5000000000 : ℝ)*x 1 + (-879605753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132355203/250000000 : ℝ)^4523 ≤ (10987780897527/25000000000000 : ℝ)^3499 := by
    have hnat : (132355203 : ℕ)^4523*25000000000000^3499 ≤ 10987780897527^3499*250000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132355203 250000000 10987780897527 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717580501/5000000000 : ℝ)^4523 ≤ (22734792505729/50000000000000 : ℝ)^3499 := by
    have hnat : (2717580501 : ℕ)^4523*50000000000000^3499 ≤ 22734792505729^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717580501 5000000000 22734792505729 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879605753/5000000000 : ℝ)^4523 ≤ (10579291391697/100000000000000 : ℝ)^3499 := by
    have hnat : (879605753 : ℕ)^4523*100000000000000^3499 ≤ 10579291391697^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879605753 5000000000 10579291391697 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132355203/250000000 : ℝ), (2717580501/5000000000 : ℝ), (-879605753/5000000000 : ℝ)] ![(10987780897527/25000000000000 : ℝ), (22734792505729/50000000000000 : ℝ), (10579291391697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132355203/250000000 : ℝ)|^4523 ≤ (10987780897527/25000000000000 : ℝ)^3499
        have hw : |(132355203/250000000 : ℝ)|=(132355203/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717580501/5000000000 : ℝ)|^4523 ≤ (22734792505729/50000000000000 : ℝ)^3499
        have hw : |(2717580501/5000000000 : ℝ)|=(2717580501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-879605753/5000000000 : ℝ)|^4523 ≤ (10579291391697/100000000000000 : ℝ)^3499
        have hw : |(-879605753/5000000000 : ℝ)|=(879605753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s3_7 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266816883/625000000 : ℝ)*x 0 + (2262003281/5000000000 : ℝ)*x 1 + (2013283697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266816883/625000000 : ℝ)^4523 ≤ (16638664534641/50000000000000 : ℝ)^3499 := by
    have hnat : (266816883 : ℕ)^4523*50000000000000^3499 ≤ 16638664534641^3499*625000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266816883 625000000 16638664534641 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262003281/5000000000 : ℝ)^4523 ≤ (1793413212679/5000000000000 : ℝ)^3499 := by
    have hnat : (2262003281 : ℕ)^4523*5000000000000^3499 ≤ 1793413212679^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262003281 5000000000 1793413212679 5000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013283697/5000000000 : ℝ)^4523 ≤ (30854406664499/100000000000000 : ℝ)^3499 := by
    have hnat : (2013283697 : ℕ)^4523*100000000000000^3499 ≤ 30854406664499^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013283697 5000000000 30854406664499 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266816883/625000000 : ℝ), (2262003281/5000000000 : ℝ), (2013283697/5000000000 : ℝ)] ![(16638664534641/50000000000000 : ℝ), (1793413212679/5000000000000 : ℝ), (30854406664499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266816883/625000000 : ℝ)|^4523 ≤ (16638664534641/50000000000000 : ℝ)^3499
        have hw : |(266816883/625000000 : ℝ)|=(266816883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262003281/5000000000 : ℝ)|^4523 ≤ (1793413212679/5000000000000 : ℝ)^3499
        have hw : |(2262003281/5000000000 : ℝ)|=(2262003281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013283697/5000000000 : ℝ)|^4523 ≤ (30854406664499/100000000000000 : ℝ)^3499
        have hw : |(2013283697/5000000000 : ℝ)|=(2013283697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1513_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (209/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (10857/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (311/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (209/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (209/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (209/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (209/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (209/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (209/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (209/2000 : ℝ) ^ (4521/1024 : ℝ) ≤ (46704648353083/1000000000000000000 : ℝ) := by
    have hpowers : (209/2000 : ℝ)^4521 ≤ (46704648353083/1000000000000000000 : ℝ)^1024 := by
      have hnat : (209 : ℕ)^4521*1000000000000000000^1024 ≤ 46704648353083^1024*2000^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        209 2000 46704648353083 1000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (209/2000 : ℝ)) (X := (46704648353083/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15993/100000 : ℝ) ^ (4521/1024 : ℝ) ≤ (7642924775527723/25000000000000000000 : ℝ) := by
    have hpowers : (15993/100000 : ℝ)^4521 ≤ (7642924775527723/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15993 : ℕ)^4521*25000000000000000000^1024 ≤ 7642924775527723^1024*100000^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15993 100000 7642924775527723 25000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15993/100000 : ℝ)) (X := (7642924775527723/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500046704648353083/500000000000000000 : ℝ) ≤ (1250026445383907/1250000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (500046704648353083/500000000000000000 : ℝ)^1024 ≤ (1250026445383907/1250000000000000 : ℝ)^4521 := by
      have hnat : (500046704648353083 : ℕ)^1024*1250000000000000^4521 ≤ 1250026445383907^4521*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500046704648353083 500000000000000000 1250026445383907 1250000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250026445383907/1250000000000000 : ℝ)) (X := (500046704648353083/500000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504405270492177399/12500000000000000000 : ℝ) ≤ (5000399060585377/5000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (12504405270492177399/12500000000000000000 : ℝ)^1024 ≤ (5000399060585377/5000000000000000 : ℝ)^4521 := by
      have hnat : (12504405270492177399 : ℕ)^1024*5000000000000000^4521 ≤ 5000399060585377^4521*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504405270492177399 12500000000000000000 5000399060585377 5000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000399060585377/5000000000000000 : ℝ)) (X := (12504405270492177399/12500000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507642924775527723/12500000000000000000 : ℝ) ≤ (2500346169817563/2500000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (12507642924775527723/12500000000000000000 : ℝ)^1024 ≤ (2500346169817563/2500000000000000 : ℝ)^4521 := by
      have hnat : (12507642924775527723 : ℕ)^1024*2500000000000000^4521 ≤ 2500346169817563^4521*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507642924775527723 12500000000000000000 2500346169817563 2500000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500346169817563/2500000000000000 : ℝ)) (X := (12507642924775527723/12500000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(46704648353083/1000000000000000000 : ℝ) ≤ ((865920525466007247/866093750000000000 : ℝ)+2*(293279049749/277150000000000 : ℝ)*(209/2000 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (865920525466007247/866093750000000000 : ℝ)+2*(293279049749/277150000000000 : ℝ)*(209/2000 : ℝ)=(1250026445383907/1250000000000000 : ℝ) by norm_num, show 1+2*(46704648353083/1000000000000000000 : ℝ)=(500046704648353083/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7642924775527723/25000000000000000000 : ℝ)+(46704648353083/1000000000000000000 : ℝ) ≤ ((865920525466007247/866093750000000000 : ℝ)+(293279049749/277150000000000 : ℝ)*((15993/100000 : ℝ)+(209/2000 : ℝ)))^(4521/1024 : ℝ) := by
    rw [show (865920525466007247/866093750000000000 : ℝ)+(293279049749/277150000000000 : ℝ)*((15993/100000 : ℝ)+(209/2000 : ℝ))=(5000399060585377/5000000000000000 : ℝ) by norm_num, show 1+(7642924775527723/25000000000000000000 : ℝ)+(46704648353083/1000000000000000000 : ℝ)=(12504405270492177399/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7642924775527723/25000000000000000000 : ℝ) ≤ ((865920525466007247/866093750000000000 : ℝ)+2*(293279049749/277150000000000 : ℝ)*(15993/100000 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (865920525466007247/866093750000000000 : ℝ)+2*(293279049749/277150000000000 : ℝ)*(15993/100000 : ℝ)=(2500346169817563/2500000000000000 : ℝ) by norm_num, show 1+2*(7642924775527723/25000000000000000000 : ℝ)=(12507642924775527723/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (865920525466007247/866093750000000000 : ℝ)*(X 1 0+X 2 0)+(293279049749/277150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (209/2000 : ℝ)) (hi := (15993/100000 : ℝ)) (c := (865920525466007247/866093750000000000 : ℝ)) (alpha := (293279049749/277150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (865920525466007247/866093750000000000 : ℝ)*(X 0 1+X 2 1)+(293279049749/277150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (209/2000 : ℝ)) (hi := (15993/100000 : ℝ)) (c := (865920525466007247/866093750000000000 : ℝ)) (alpha := (293279049749/277150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (865920525466007247/866093750000000000 : ℝ)*(X 0 2+X 1 2)+(293279049749/277150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (209/2000 : ℝ)) (hi := (15993/100000 : ℝ)) (c := (865920525466007247/866093750000000000 : ℝ)) (alpha := (293279049749/277150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-933024193/5000000000 : ℝ)*X 0 0+(2718171409/5000000000 : ℝ)*X 0 1+(651846617/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107047659/200000000 : ℝ)*X 1 0+(-989799909/5000000000 : ℝ)*X 1 1+(5214773117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83630987/156250000 : ℝ)*X 2 0+(208590919/400000000 : ℝ)*X 2 1+(-494899929/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268998783/10000000000 : ℝ)*X 0 0+(1005971309/2500000000 : ℝ)*X 0 1+(4526668489/10000000000 : ℝ)*X 0 2+(4268998783/10000000000 : ℝ)*X 1 0+(1005971309/2500000000 : ℝ)*X 1 1+(4526668489/10000000000 : ℝ)*X 1 2+(4268998783/10000000000 : ℝ)*X 2 0+(1005971309/2500000000 : ℝ)*X 2 1+(4526668489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-46651981/250000000 : ℝ)*X 0 0+(5215946209/10000000000 : ℝ)*X 0 1+(5435161107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058841573/2000000000 : ℝ)*X 1 0+(-1759211379/10000000000 : ℝ)*X 1 1+(1087032269/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132355203/250000000 : ℝ)*X 2 0+(2717580501/5000000000 : ℝ)*X 2 1+(-879605753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((266816883/625000000 : ℝ)*X 0 0+(2262003281/5000000000 : ℝ)*X 0 1+(2013283697/5000000000 : ℝ)*X 0 2+(266816883/625000000 : ℝ)*X 1 0+(2262003281/5000000000 : ℝ)*X 1 1+(2013283697/5000000000 : ℝ)*X 1 2+(266816883/625000000 : ℝ)*X 2 0+(2262003281/5000000000 : ℝ)*X 2 1+(2013283697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51200718041442612354624141/5413085937500000000000000000000 : ℝ) := by norm_num
    linear_combination (553911307/25000000000000 : ℝ)*(base19) + (131663587/6250000000000 : ℝ)*(base23) + (394281151/100000000000000 : ℝ)*(upper3) + (31349217/20000000000000 : ℝ)*(upper4) + (314835047/100000000000000 : ℝ)*(upper5) + (1625568781943757/50000000000000 : ℝ)*(major0) + (1625568781943757/50000000000000 : ℝ)*(major1) + (1625568781943757/50000000000000 : ℝ)*(major2) + (225664034182473/5000000000000 : ℝ)*(sp0) + (4513312392073327/100000000000000 : ℝ)*(sp1) + (4513312501101163/100000000000000 : ℝ)*(sp2) + (198894328770183/10000000000000 : ℝ)*(sp3) + (6784813819/20000000000000 : ℝ)*(sp4) + (8458532433/50000000000000 : ℝ)*(sp7) + (248620025595837/12500000000000 : ℝ)*(f.failure) + (902662921543711/20000000000000 : ℝ)*(f.sum) + (18905667575851/13857500000000000000000000000 : ℝ)*base65 + (804974476780817083/86609375000000000000000000000000 : ℝ)*base67 + (315900422172129583/86609375000000000000000000000000 : ℝ)*base69 + (203323355371833177/21652343750000000000000000000000 : ℝ)*base71 + (63096657107241/13857500000000000000000000000 : ℝ)*base73 + (186969589657098333/86609375000000000000000000000000 : ℝ)*base75 + (158863796090838229/43304687500000000000000000000000 : ℝ)*base77 + (1607533253046910833/86609375000000000000000000000000 : ℝ)*base79 + (65228407882141/13857500000000000000000000000 : ℝ)*base81 + (2966607/312500000000000000000 : ℝ)*base90 + (2966607/312500000000000000000 : ℝ)*base92 + (2966607/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38520826766407151935389/3464375000000000000000000000 : ℝ) := by norm_num
    linear_combination (367790283/20000000000000 : ℝ)*(base19) + (1158323667/50000000000000 : ℝ)*(base23) + (34233491/12500000000000 : ℝ)*(upper3) + (118950331/100000000000000 : ℝ)*(lower4) + (102237857/50000000000000 : ℝ)*(upper5) + (3286013917934833/100000000000000 : ℝ)*(major0) + (3286013917934833/100000000000000 : ℝ)*(major1) + (3286013917934833/100000000000000 : ℝ)*(major2) + (30589334163/100000000000000 : ℝ)*(sp1) + (1680973711/5000000000000 : ℝ)*(sp2) + (2280865413504803/50000000000000 : ℝ)*(sp4) + (4561698398724029/100000000000000 : ℝ)*(sp5) + (1140423722722013/25000000000000 : ℝ)*(sp6) + (502574159555619/25000000000000 : ℝ)*(sp7) + (502574159555619/25000000000000 : ℝ)*(f.failure) + (2280865413504803/50000000000000 : ℝ)*(f.sum) + (18497049833043/13857500000000000000000000000 : ℝ)*base66 + (272951856740965437/43304687500000000000000000000000 : ℝ)*base68 + (389212748497628313/43304687500000000000000000000000 : ℝ)*base69 + (380309593567415249/86609375000000000000000000000000 : ℝ)*base72 + (49570105153871/27715000000000000000000000000 : ℝ)*base74 + (113700509032678031/21652343750000000000000000000000 : ℝ)*base76 + (8137030384356297/10826171875000000000000000000000 : ℝ)*base77 + (29790926356665719/21652343750000000000000000000000 : ℝ)*base79 + (63410721747877/13857500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2050609/625000000000000000000 : ℝ)*base90 + (2050609/625000000000000000000 : ℝ)*base92 + (2050609/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1513_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (209/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10857/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (311/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1513_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1513_s4_0 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-373296293/2000000000 : ℝ)*x 0 + (271674827/500000000 : ℝ)*x 1 + (130433327/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (373296293/2000000000 : ℝ)^4523 ≤ (11420499122639/100000000000000 : ℝ)^3499 := by
    have hnat : (373296293 : ℕ)^4523*100000000000000^3499 ≤ 11420499122639^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373296293 2000000000 11420499122639 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271674827/500000000 : ℝ)^4523 ≤ (45451586124731/100000000000000 : ℝ)^3499 := by
    have hnat : (271674827 : ℕ)^4523*100000000000000^3499 ≤ 45451586124731^3499*500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271674827 500000000 45451586124731 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130433327/250000000 : ℝ)^4523 ≤ (8625582947453/20000000000000 : ℝ)^3499 := by
    have hnat : (130433327 : ℕ)^4523*20000000000000^3499 ≤ 8625582947453^3499*250000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130433327 250000000 8625582947453 20000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-373296293/2000000000 : ℝ), (271674827/500000000 : ℝ), (130433327/250000000 : ℝ)] ![(11420499122639/100000000000000 : ℝ), (45451586124731/100000000000000 : ℝ), (8625582947453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-373296293/2000000000 : ℝ)|^4523 ≤ (11420499122639/100000000000000 : ℝ)^3499
        have hw : |(-373296293/2000000000 : ℝ)|=(373296293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271674827/500000000 : ℝ)|^4523 ≤ (45451586124731/100000000000000 : ℝ)^3499
        have hw : |(271674827/500000000 : ℝ)|=(271674827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130433327/250000000 : ℝ)|^4523 ≤ (8625582947453/20000000000000 : ℝ)^3499
        have hw : |(130433327/250000000 : ℝ)|=(130433327/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s4_1 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351638337/10000000000 : ℝ)*x 0 + (-494299279/2500000000 : ℝ)*x 1 + (5217332547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351638337/10000000000 : ℝ)^4523 ≤ (44568399234969/100000000000000 : ℝ)^3499 := by
    have hnat : (5351638337 : ℕ)^4523*100000000000000^3499 ≤ 44568399234969^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351638337 10000000000 44568399234969 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494299279/2500000000 : ℝ)^4523 ≤ (1537961463761/12500000000000 : ℝ)^3499 := by
    have hnat : (494299279 : ℕ)^4523*12500000000000^3499 ≤ 1537961463761^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494299279 2500000000 1537961463761 12500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217332547/10000000000 : ℝ)^4523 ≤ (10781977260481/25000000000000 : ℝ)^3499 := by
    have hnat : (5217332547 : ℕ)^4523*25000000000000^3499 ≤ 10781977260481^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217332547 10000000000 10781977260481 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351638337/10000000000 : ℝ), (-494299279/2500000000 : ℝ), (5217332547/10000000000 : ℝ)] ![(44568399234969/100000000000000 : ℝ), (1537961463761/12500000000000 : ℝ), (10781977260481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351638337/10000000000 : ℝ)|^4523 ≤ (44568399234969/100000000000000 : ℝ)^3499
        have hw : |(5351638337/10000000000 : ℝ)|=(5351638337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-494299279/2500000000 : ℝ)|^4523 ≤ (1537961463761/12500000000000 : ℝ)^3499
        have hw : |(-494299279/2500000000 : ℝ)|=(494299279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217332547/10000000000 : ℝ)|^4523 ≤ (10781977260481/25000000000000 : ℝ)^3499
        have hw : |(5217332547/10000000000 : ℝ)|=(5217332547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s4_2 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675818977/5000000000 : ℝ)*x 0 + (1043466617/2000000000 : ℝ)*x 1 + (-988598457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675818977/5000000000 : ℝ)^4523 ≤ (44568395111889/100000000000000 : ℝ)^3499 := by
    have hnat : (2675818977 : ℕ)^4523*100000000000000^3499 ≤ 44568395111889^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675818977 5000000000 44568395111889 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043466617/2000000000 : ℝ)^4523 ≤ (10781978697673/25000000000000 : ℝ)^3499 := by
    have hnat : (1043466617 : ℕ)^4523*25000000000000^3499 ≤ 10781978697673^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043466617 2000000000 10781978697673 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988598457/5000000000 : ℝ)^4523 ≤ (2460738017043/20000000000000 : ℝ)^3499 := by
    have hnat : (988598457 : ℕ)^4523*20000000000000^3499 ≤ 2460738017043^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988598457 5000000000 2460738017043 20000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675818977/5000000000 : ℝ), (1043466617/2000000000 : ℝ), (-988598457/5000000000 : ℝ)] ![(44568395111889/100000000000000 : ℝ), (10781978697673/25000000000000 : ℝ), (2460738017043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675818977/5000000000 : ℝ)|^4523 ≤ (44568395111889/100000000000000 : ℝ)^3499
        have hw : |(2675818977/5000000000 : ℝ)|=(2675818977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043466617/2000000000 : ℝ)|^4523 ≤ (10781978697673/25000000000000 : ℝ)^3499
        have hw : |(1043466617/2000000000 : ℝ)|=(1043466617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988598457/5000000000 : ℝ)|^4523 ≤ (2460738017043/20000000000000 : ℝ)^3499
        have hw : |(-988598457/5000000000 : ℝ)|=(988598457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s4_3 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4269269591/10000000000 : ℝ)*x 0 + (2014994071/5000000000 : ℝ)*x 1 + (904100709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269269591/10000000000 : ℝ)^4523 ≤ (33279338916909/100000000000000 : ℝ)^3499 := by
    have hnat : (4269269591 : ℕ)^4523*100000000000000^3499 ≤ 33279338916909^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269269591 10000000000 33279338916909 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014994071/5000000000 : ℝ)^4523 ≤ (1235531767819/4000000000000 : ℝ)^3499 := by
    have hnat : (2014994071 : ℕ)^4523*4000000000000^3499 ≤ 1235531767819^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014994071 5000000000 1235531767819 4000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904100709/2000000000 : ℝ)^4523 ≤ (17916183434589/50000000000000 : ℝ)^3499 := by
    have hnat : (904100709 : ℕ)^4523*50000000000000^3499 ≤ 17916183434589^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904100709 2000000000 17916183434589 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269269591/10000000000 : ℝ), (2014994071/5000000000 : ℝ), (904100709/2000000000 : ℝ)] ![(33279338916909/100000000000000 : ℝ), (1235531767819/4000000000000 : ℝ), (17916183434589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269269591/10000000000 : ℝ)|^4523 ≤ (33279338916909/100000000000000 : ℝ)^3499
        have hw : |(4269269591/10000000000 : ℝ)|=(4269269591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014994071/5000000000 : ℝ)|^4523 ≤ (1235531767819/4000000000000 : ℝ)^3499
        have hw : |(2014994071/5000000000 : ℝ)|=(2014994071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904100709/2000000000 : ℝ)|^4523 ≤ (17916183434589/50000000000000 : ℝ)^3499
        have hw : |(904100709/2000000000 : ℝ)|=(904100709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s4_4 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-233313849/1250000000 : ℝ)*x 0 + (2609224797/5000000000 : ℝ)*x 1 + (5432371693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233313849/1250000000 : ℝ)^4523 ≤ (5710365541209/50000000000000 : ℝ)^3499 := by
    have hnat : (233313849 : ℕ)^4523*50000000000000^3499 ≤ 5710365541209^3499*1250000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233313849 1250000000 5710365541209 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609224797/5000000000 : ℝ)^4523 ≤ (21569922778911/50000000000000 : ℝ)^3499 := by
    have hnat : (2609224797 : ℕ)^4523*50000000000000^3499 ≤ 21569922778911^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609224797 5000000000 21569922778911 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432371693/10000000000 : ℝ)^4523 ≤ (45439423352011/100000000000000 : ℝ)^3499 := by
    have hnat : (5432371693 : ℕ)^4523*100000000000000^3499 ≤ 45439423352011^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432371693 10000000000 45439423352011 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-233313849/1250000000 : ℝ), (2609224797/5000000000 : ℝ), (5432371693/10000000000 : ℝ)] ![(5710365541209/50000000000000 : ℝ), (21569922778911/50000000000000 : ℝ), (45439423352011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-233313849/1250000000 : ℝ)|^4523 ≤ (5710365541209/50000000000000 : ℝ)^3499
        have hw : |(-233313849/1250000000 : ℝ)|=(233313849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609224797/5000000000 : ℝ)|^4523 ≤ (21569922778911/50000000000000 : ℝ)^3499
        have hw : |(2609224797/5000000000 : ℝ)|=(2609224797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432371693/10000000000 : ℝ)|^4523 ≤ (45439423352011/100000000000000 : ℝ)^3499
        have hw : |(5432371693/10000000000 : ℝ)|=(5432371693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s4_5 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647441797/5000000000 : ℝ)*x 0 + (-440539573/2500000000 : ℝ)*x 1 + (679046463/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647441797/5000000000 : ℝ)^4523 ≤ (43958372427579/100000000000000 : ℝ)^3499 := by
    have hnat : (2647441797 : ℕ)^4523*100000000000000^3499 ≤ 43958372427579^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647441797 5000000000 43958372427579 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440539573/2500000000 : ℝ)^4523 ≤ (10602204085923/100000000000000 : ℝ)^3499 := by
    have hnat : (440539573 : ℕ)^4523*100000000000000^3499 ≤ 10602204085923^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440539573 2500000000 10602204085923 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679046463/1250000000 : ℝ)^4523 ≤ (45439423470949/100000000000000 : ℝ)^3499 := by
    have hnat : (679046463 : ℕ)^4523*100000000000000^3499 ≤ 45439423470949^3499*1250000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679046463 1250000000 45439423470949 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647441797/5000000000 : ℝ), (-440539573/2500000000 : ℝ), (679046463/1250000000 : ℝ)] ![(43958372427579/100000000000000 : ℝ), (10602204085923/100000000000000 : ℝ), (45439423470949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647441797/5000000000 : ℝ)|^4523 ≤ (43958372427579/100000000000000 : ℝ)^3499
        have hw : |(2647441797/5000000000 : ℝ)|=(2647441797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440539573/2500000000 : ℝ)|^4523 ≤ (10602204085923/100000000000000 : ℝ)^3499
        have hw : |(-440539573/2500000000 : ℝ)|=(440539573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679046463/1250000000 : ℝ)|^4523 ≤ (45439423470949/100000000000000 : ℝ)^3499
        have hw : |(679046463/1250000000 : ℝ)|=(679046463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s4_6 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323720921/2500000000 : ℝ)*x 0 + (2716185831/5000000000 : ℝ)*x 1 + (-1762158227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323720921/2500000000 : ℝ)^4523 ≤ (4395837339343/10000000000000 : ℝ)^3499 := by
    have hnat : (1323720921 : ℕ)^4523*10000000000000^3499 ≤ 4395837339343^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323720921 2500000000 4395837339343 10000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716185831/5000000000 : ℝ)^4523 ≤ (5679927877103/12500000000000 : ℝ)^3499 := by
    have hnat : (2716185831 : ℕ)^4523*12500000000000^3499 ≤ 5679927877103^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716185831 5000000000 5679927877103 12500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1762158227/10000000000 : ℝ)^4523 ≤ (10602203580393/100000000000000 : ℝ)^3499 := by
    have hnat : (1762158227 : ℕ)^4523*100000000000000^3499 ≤ 10602203580393^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762158227 10000000000 10602203580393 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323720921/2500000000 : ℝ), (2716185831/5000000000 : ℝ), (-1762158227/10000000000 : ℝ)] ![(4395837339343/10000000000000 : ℝ), (5679927877103/12500000000000 : ℝ), (10602203580393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323720921/2500000000 : ℝ)|^4523 ≤ (4395837339343/10000000000000 : ℝ)^3499
        have hw : |(1323720921/2500000000 : ℝ)|=(1323720921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716185831/5000000000 : ℝ)|^4523 ≤ (5679927877103/12500000000000 : ℝ)^3499
        have hw : |(2716185831/5000000000 : ℝ)|=(2716185831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1762158227/10000000000 : ℝ)|^4523 ≤ (10602203580393/100000000000000 : ℝ)^3499
        have hw : |(-1762158227/10000000000 : ℝ)|=(1762158227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s4_7 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4269336177/10000000000 : ℝ)*x 0 + (4517969131/10000000000 : ℝ)*x 1 + (2016270513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269336177/10000000000 : ℝ)^4523 ≤ (1040000308221/3125000000000 : ℝ)^3499 := by
    have hnat : (4269336177 : ℕ)^4523*3125000000000^3499 ≤ 1040000308221^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269336177 10000000000 1040000308221 3125000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517969131/10000000000 : ℝ)^4523 ≤ (17903200189503/50000000000000 : ℝ)^3499 := by
    have hnat : (4517969131 : ℕ)^4523*50000000000000^3499 ≤ 17903200189503^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517969131 10000000000 17903200189503 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016270513/5000000000 : ℝ)^4523 ≤ (154567948729/500000000000 : ℝ)^3499 := by
    have hnat : (2016270513 : ℕ)^4523*500000000000^3499 ≤ 154567948729^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016270513 5000000000 154567948729 500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269336177/10000000000 : ℝ), (4517969131/10000000000 : ℝ), (2016270513/5000000000 : ℝ)] ![(1040000308221/3125000000000 : ℝ), (17903200189503/50000000000000 : ℝ), (154567948729/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269336177/10000000000 : ℝ)|^4523 ≤ (1040000308221/3125000000000 : ℝ)^3499
        have hw : |(4269336177/10000000000 : ℝ)|=(4269336177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517969131/10000000000 : ℝ)|^4523 ≤ (17903200189503/50000000000000 : ℝ)^3499
        have hw : |(4517969131/10000000000 : ℝ)|=(4517969131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016270513/5000000000 : ℝ)|^4523 ≤ (154567948729/500000000000 : ℝ)^3499
        have hw : |(2016270513/5000000000 : ℝ)|=(2016270513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1513_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (311/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10857/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (341/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (311/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10857/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (311/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10857/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (311/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10857/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (311/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10857/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (311/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10857/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (311/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10857/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10857/100000 : ℝ) ^ (4521/1024 : ℝ) ≤ (2764338807965271/50000000000000000000 : ℝ) := by
    have hpowers : (10857/100000 : ℝ)^4521 ≤ (2764338807965271/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10857 : ℕ)^4521*50000000000000000000^1024 ≤ 2764338807965271^1024*100000^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10857 100000 2764338807965271 50000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10857/100000 : ℝ)) (X := (2764338807965271/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (311/2000 : ℝ) ^ (4521/1024 : ℝ) ≤ (5401173265383073/20000000000000000000 : ℝ) := by
    have hpowers : (311/2000 : ℝ)^4521 ≤ (5401173265383073/20000000000000000000 : ℝ)^1024 := by
      have hnat : (311 : ℕ)^4521*20000000000000000000^1024 ≤ 5401173265383073^1024*2000^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        311 2000 5401173265383073 20000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (311/2000 : ℝ)) (X := (5401173265383073/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002764338807965271/25000000000000000000 : ℝ) ≤ (1000025043679671/1000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (25002764338807965271/25000000000000000000 : ℝ)^1024 ≤ (1000025043679671/1000000000000000 : ℝ)^4521 := by
      have hnat : (25002764338807965271 : ℕ)^1024*1000000000000000^4521 ≤ 1000025043679671^4521*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002764338807965271 25000000000000000000 1000025043679671 1000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000025043679671/1000000000000000 : ℝ)) (X := (25002764338807965271/25000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032534543942845907/100000000000000000000 : ℝ) ≤ (125009210125473/125000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (100032534543942845907/100000000000000000000 : ℝ)^1024 ≤ (125009210125473/125000000000000 : ℝ)^4521 := by
      have hnat : (100032534543942845907 : ℕ)^1024*125000000000000^4521 ≤ 125009210125473^4521*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032534543942845907 100000000000000000000 125009210125473 125000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125009210125473/125000000000000 : ℝ)) (X := (100032534543942845907/100000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005401173265383073/10000000000000000000 : ℝ) ≤ (1000122318327897/1000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (10005401173265383073/10000000000000000000 : ℝ)^1024 ≤ (1000122318327897/1000000000000000 : ℝ)^4521 := by
      have hnat : (10005401173265383073 : ℕ)^1024*1000000000000000^4521 ≤ 1000122318327897^4521*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005401173265383073 10000000000000000000 1000122318327897 1000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000122318327897/1000000000000000 : ℝ)) (X := (10005401173265383073/10000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2764338807965271/50000000000000000000 : ℝ) ≤ ((4692061419132906321/4693000000000000000 : ℝ)+2*(48637324113/46930000000000 : ℝ)*(10857/100000 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (4692061419132906321/4693000000000000000 : ℝ)+2*(48637324113/46930000000000 : ℝ)*(10857/100000 : ℝ)=(1000025043679671/1000000000000000 : ℝ) by norm_num, show 1+2*(2764338807965271/50000000000000000000 : ℝ)=(25002764338807965271/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5401173265383073/20000000000000000000 : ℝ)+(2764338807965271/50000000000000000000 : ℝ) ≤ ((4692061419132906321/4693000000000000000 : ℝ)+(48637324113/46930000000000 : ℝ)*((311/2000 : ℝ)+(10857/100000 : ℝ)))^(4521/1024 : ℝ) := by
    rw [show (4692061419132906321/4693000000000000000 : ℝ)+(48637324113/46930000000000 : ℝ)*((311/2000 : ℝ)+(10857/100000 : ℝ))=(125009210125473/125000000000000 : ℝ) by norm_num, show 1+(5401173265383073/20000000000000000000 : ℝ)+(2764338807965271/50000000000000000000 : ℝ)=(100032534543942845907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5401173265383073/20000000000000000000 : ℝ) ≤ ((4692061419132906321/4693000000000000000 : ℝ)+2*(48637324113/46930000000000 : ℝ)*(311/2000 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (4692061419132906321/4693000000000000000 : ℝ)+2*(48637324113/46930000000000 : ℝ)*(311/2000 : ℝ)=(1000122318327897/1000000000000000 : ℝ) by norm_num, show 1+2*(5401173265383073/20000000000000000000 : ℝ)=(10005401173265383073/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4692061419132906321/4693000000000000000 : ℝ)*(X 1 0+X 2 0)+(48637324113/46930000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (10857/100000 : ℝ)) (hi := (311/2000 : ℝ)) (c := (4692061419132906321/4693000000000000000 : ℝ)) (alpha := (48637324113/46930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4692061419132906321/4693000000000000000 : ℝ)*(X 0 1+X 2 1)+(48637324113/46930000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (10857/100000 : ℝ)) (hi := (311/2000 : ℝ)) (c := (4692061419132906321/4693000000000000000 : ℝ)) (alpha := (48637324113/46930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4692061419132906321/4693000000000000000 : ℝ)*(X 0 2+X 1 2)+(48637324113/46930000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (10857/100000 : ℝ)) (hi := (311/2000 : ℝ)) (c := (4692061419132906321/4693000000000000000 : ℝ)) (alpha := (48637324113/46930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-373296293/2000000000 : ℝ)*X 0 0+(271674827/500000000 : ℝ)*X 0 1+(130433327/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351638337/10000000000 : ℝ)*X 1 0+(-494299279/2500000000 : ℝ)*X 1 1+(5217332547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675818977/5000000000 : ℝ)*X 2 0+(1043466617/2000000000 : ℝ)*X 2 1+(-988598457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4269269591/10000000000 : ℝ)*X 0 0+(2014994071/5000000000 : ℝ)*X 0 1+(904100709/2000000000 : ℝ)*X 0 2+(4269269591/10000000000 : ℝ)*X 1 0+(2014994071/5000000000 : ℝ)*X 1 1+(904100709/2000000000 : ℝ)*X 1 2+(4269269591/10000000000 : ℝ)*X 2 0+(2014994071/5000000000 : ℝ)*X 2 1+(904100709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-233313849/1250000000 : ℝ)*X 0 0+(2609224797/5000000000 : ℝ)*X 0 1+(5432371693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647441797/5000000000 : ℝ)*X 1 0+(-440539573/2500000000 : ℝ)*X 1 1+(679046463/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323720921/2500000000 : ℝ)*X 2 0+(2716185831/5000000000 : ℝ)*X 2 1+(-1762158227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4269336177/10000000000 : ℝ)*X 0 0+(4517969131/10000000000 : ℝ)*X 0 1+(2016270513/5000000000 : ℝ)*X 0 2+(4269336177/10000000000 : ℝ)*X 1 0+(4517969131/10000000000 : ℝ)*X 1 1+(2016270513/5000000000 : ℝ)*X 1 2+(4269336177/10000000000 : ℝ)*X 2 0+(4517969131/10000000000 : ℝ)*X 2 1+(2016270513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1061149050192320353436448993/117325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1780120563/100000000000000 : ℝ)*(base19) + (635869157/50000000000000 : ℝ)*(base23) + (94885463/100000000000000 : ℝ)*(lower2) + (137638043/100000000000000 : ℝ)*(upper3) + (18533769/12500000000000 : ℝ)*(upper5) + (1666216741721937/50000000000000 : ℝ)*(major0) + (1666216741721937/50000000000000 : ℝ)*(major1) + (1666216741721937/50000000000000 : ℝ)*(major2) + (2313075018493983/50000000000000 : ℝ)*(sp0) + (578271247664159/12500000000000 : ℝ)*(sp1) + (28913565560597/625000000000 : ℝ)*(sp2) + (1019341777779281/50000000000000 : ℝ)*(sp3) + (21724445869/100000000000000 : ℝ)*(sp4) + (11348411133/100000000000000 : ℝ)*(sp7) + (407738980793939/20000000000000 : ℝ)*(f.failure) + (2313085880716917/50000000000000 : ℝ)*(f.sum) + (7876428563739/4693000000000000000000000000 : ℝ)*base65 + (89420085976668171/18050000000000000000000000000000 : ℝ)*base68 + (385472110142268171/18050000000000000000000000000000 : ℝ)*base70 + (107520324433368171/18050000000000000000000000000000 : ℝ)*base72 + (3798186080749/4693000000000000000000000000 : ℝ)*base73 + (247724659422618171/18050000000000000000000000000000 : ℝ)*base76 + (120040840792168171/18050000000000000000000000000000 : ℝ)*base78 + (50280725427368171/18050000000000000000000000000000 : ℝ)*base80 + (80119029979/23465000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (286129/500000000000000000000 : ℝ)*base90 + (286129/500000000000000000000 : ℝ)*base92 + (286129/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74685628101343144758261813/14665625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190109781/25000000000000 : ℝ)*(base19) + (203287531/20000000000000 : ℝ)*(base23) + (21056891/25000000000000 : ℝ)*(upper3) + (39225059/50000000000000 : ℝ)*(lower4) + (4497173/3125000000000 : ℝ)*(upper5) + (26307173357661/781250000000 : ℝ)*(major0) + (26307173357661/781250000000 : ℝ)*(major1) + (26307173357661/781250000000 : ℝ)*(major2) + (2494939293/20000000000000 : ℝ)*(sp1) + (3024496809/20000000000000 : ℝ)*(sp2) + (4674599762673263/100000000000000 : ℝ)*(sp4) + (2337293263768837/50000000000000 : ℝ)*(sp5) + (4674583623751563/100000000000000 : ℝ)*(sp6) + (1030018223567913/50000000000000 : ℝ)*(sp7) + (1030018223567913/50000000000000 : ℝ)*(f.failure) + (4674599762673263/100000000000000 : ℝ)*(f.sum) + (22390493929/93860000000000000000000000 : ℝ)*base66 + (1002507005403719/141015625000000000000000000000 : ℝ)*base68 + (3769223855189127/1128125000000000000000000000000 : ℝ)*base70 + (2286116869589127/1128125000000000000000000000000 : ℝ)*base72 + (5864775022507/2346500000000000000000000000 : ℝ)*base73 + (10417014704289127/1128125000000000000000000000000 : ℝ)*base76 + (565693275633187/282031250000000000000000000000 : ℝ)*base77 + (8782139801195377/1128125000000000000000000000000 : ℝ)*base80 + (10184135350723/4693000000000000000000000000 : ℝ)*base81 + (8084643/1250000000000000000000 : ℝ)*base90 + (8084643/1250000000000000000000 : ℝ)*base92 + (8084643/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1513_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (311/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10857/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (341/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1513_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1513_s5_0 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-933267867/5000000000 : ℝ)*x 0 + (5433144737/10000000000 : ℝ)*x 1 + (5217648911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933267867/5000000000 : ℝ)^4523 ≤ (11420928360197/100000000000000 : ℝ)^3499 := by
    have hnat : (933267867 : ℕ)^4523*100000000000000^3499 ≤ 11420928360197^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933267867 5000000000 11420928360197 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433144737/10000000000 : ℝ)^4523 ≤ (45447782061583/100000000000000 : ℝ)^3499 := by
    have hnat : (5433144737 : ℕ)^4523*100000000000000^3499 ≤ 45447782061583^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433144737 10000000000 45447782061583 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217648911/10000000000 : ℝ)^4523 ≤ (8626257912277/20000000000000 : ℝ)^3499 := by
    have hnat : (5217648911 : ℕ)^4523*20000000000000^3499 ≤ 8626257912277^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217648911 10000000000 8626257912277 20000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933267867/5000000000 : ℝ), (5433144737/10000000000 : ℝ), (5217648911/10000000000 : ℝ)] ![(11420928360197/100000000000000 : ℝ), (45447782061583/100000000000000 : ℝ), (8626257912277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933267867/5000000000 : ℝ)|^4523 ≤ (11420928360197/100000000000000 : ℝ)^3499
        have hw : |(-933267867/5000000000 : ℝ)|=(933267867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433144737/10000000000 : ℝ)|^4523 ≤ (45447782061583/100000000000000 : ℝ)^3499
        have hw : |(5433144737/10000000000 : ℝ)|=(5433144737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217648911/10000000000 : ℝ)|^4523 ≤ (8626257912277/20000000000000 : ℝ)^3499
        have hw : |(5217648911/10000000000 : ℝ)|=(5217648911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s5_1 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675772771/5000000000 : ℝ)*x 0 + (-395380183/2000000000 : ℝ)*x 1 + (1043529801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675772771/5000000000 : ℝ)^4523 ≤ (22283700139439/50000000000000 : ℝ)^3499 := by
    have hnat : (2675772771 : ℕ)^4523*50000000000000^3499 ≤ 22283700139439^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675772771 5000000000 22283700139439 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395380183/2000000000 : ℝ)^4523 ≤ (2460261828623/20000000000000 : ℝ)^3499 := by
    have hnat : (395380183 : ℕ)^4523*20000000000000^3499 ≤ 2460261828623^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395380183 2000000000 2460261828623 20000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043529801/2000000000 : ℝ)^4523 ≤ (21565645282917/50000000000000 : ℝ)^3499 := by
    have hnat : (1043529801 : ℕ)^4523*50000000000000^3499 ≤ 21565645282917^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043529801 2000000000 21565645282917 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675772771/5000000000 : ℝ), (-395380183/2000000000 : ℝ), (1043529801/2000000000 : ℝ)] ![(22283700139439/50000000000000 : ℝ), (2460261828623/20000000000000 : ℝ), (21565645282917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675772771/5000000000 : ℝ)|^4523 ≤ (22283700139439/50000000000000 : ℝ)^3499
        have hw : |(2675772771/5000000000 : ℝ)|=(2675772771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395380183/2000000000 : ℝ)|^4523 ≤ (2460261828623/20000000000000 : ℝ)^3499
        have hw : |(-395380183/2000000000 : ℝ)|=(395380183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043529801/2000000000 : ℝ)|^4523 ≤ (21565645282917/50000000000000 : ℝ)^3499
        have hw : |(1043529801/2000000000 : ℝ)|=(1043529801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s5_2 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351545567/10000000000 : ℝ)*x 0 + (1304412241/2500000000 : ℝ)*x 1 + (-1976900937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351545567/10000000000 : ℝ)^4523 ≤ (44567400548007/100000000000000 : ℝ)^3499 := by
    have hnat : (5351545567 : ℕ)^4523*100000000000000^3499 ≤ 44567400548007^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351545567 10000000000 44567400548007 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304412241/2500000000 : ℝ)^4523 ≤ (43131290127723/100000000000000 : ℝ)^3499 := by
    have hnat : (1304412241 : ℕ)^4523*100000000000000^3499 ≤ 43131290127723^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304412241 2500000000 43131290127723 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1976900937/10000000000 : ℝ)^4523 ≤ (6150654660037/50000000000000 : ℝ)^3499 := by
    have hnat : (1976900937 : ℕ)^4523*50000000000000^3499 ≤ 6150654660037^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976900937 10000000000 6150654660037 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351545567/10000000000 : ℝ), (1304412241/2500000000 : ℝ), (-1976900937/10000000000 : ℝ)] ![(44567400548007/100000000000000 : ℝ), (43131290127723/100000000000000 : ℝ), (6150654660037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351545567/10000000000 : ℝ)|^4523 ≤ (44567400548007/100000000000000 : ℝ)^3499
        have hw : |(5351545567/10000000000 : ℝ)|=(5351545567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304412241/2500000000 : ℝ)|^4523 ≤ (43131290127723/100000000000000 : ℝ)^3499
        have hw : |(1304412241/2500000000 : ℝ)|=(1304412241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1976900937/10000000000 : ℝ)|^4523 ≤ (6150654660037/50000000000000 : ℝ)^3499
        have hw : |(-1976900937/10000000000 : ℝ)|=(1976900937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s5_3 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4269302819/10000000000 : ℝ)*x 0 + (4030742279/10000000000 : ℝ)*x 1 + (2259870811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269302819/10000000000 : ℝ)^4523 ≤ (16639836867321/50000000000000 : ℝ)^3499 := by
    have hnat : (4269302819 : ℕ)^4523*50000000000000^3499 ≤ 16639836867321^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269302819 10000000000 16639836867321 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030742279/10000000000 : ℝ)^4523 ≤ (7723941540607/25000000000000 : ℝ)^3499 := by
    have hnat : (4030742279 : ℕ)^4523*25000000000000^3499 ≤ 7723941540607^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030742279 10000000000 7723941540607 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259870811/5000000000 : ℝ)^4523 ≤ (35824560093523/100000000000000 : ℝ)^3499 := by
    have hnat : (2259870811 : ℕ)^4523*100000000000000^3499 ≤ 35824560093523^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259870811 5000000000 35824560093523 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269302819/10000000000 : ℝ), (4030742279/10000000000 : ℝ), (2259870811/5000000000 : ℝ)] ![(16639836867321/50000000000000 : ℝ), (7723941540607/25000000000000 : ℝ), (35824560093523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269302819/10000000000 : ℝ)|^4523 ≤ (16639836867321/50000000000000 : ℝ)^3499
        have hw : |(4269302819/10000000000 : ℝ)|=(4269302819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030742279/10000000000 : ℝ)|^4523 ≤ (7723941540607/25000000000000 : ℝ)^3499
        have hw : |(4030742279/10000000000 : ℝ)|=(4030742279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259870811/5000000000 : ℝ)|^4523 ≤ (35824560093523/100000000000000 : ℝ)^3499
        have hw : |(2259870811/5000000000 : ℝ)|=(2259870811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s5_4 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1866564349/10000000000 : ℝ)*x 0 + (1304689903/2500000000 : ℝ)*x 1 + (1086405223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1866564349/10000000000 : ℝ)^4523 ≤ (11421154690377/100000000000000 : ℝ)^3499 := by
    have hnat : (1866564349 : ℕ)^4523*100000000000000^3499 ≤ 11421154690377^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866564349 10000000000 11421154690377 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304689903/2500000000 : ℝ)^4523 ≤ (21571579236909/50000000000000 : ℝ)^3499 := by
    have hnat : (1304689903 : ℕ)^4523*50000000000000^3499 ≤ 21571579236909^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304689903 2500000000 21571579236909 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086405223/2000000000 : ℝ)^4523 ≤ (22717843412943/50000000000000 : ℝ)^3499 := by
    have hnat : (1086405223 : ℕ)^4523*50000000000000^3499 ≤ 22717843412943^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086405223 2000000000 22717843412943 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1866564349/10000000000 : ℝ), (1304689903/2500000000 : ℝ), (1086405223/2000000000 : ℝ)] ![(11421154690377/100000000000000 : ℝ), (21571579236909/50000000000000 : ℝ), (22717843412943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1866564349/10000000000 : ℝ)|^4523 ≤ (11421154690377/100000000000000 : ℝ)^3499
        have hw : |(-1866564349/10000000000 : ℝ)|=(1866564349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304689903/2500000000 : ℝ)|^4523 ≤ (21571579236909/50000000000000 : ℝ)^3499
        have hw : |(1304689903/2500000000 : ℝ)|=(1304689903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086405223/2000000000 : ℝ)|^4523 ≤ (22717843412943/50000000000000 : ℝ)^3499
        have hw : |(1086405223/2000000000 : ℝ)|=(1086405223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s5_5 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647483241/5000000000 : ℝ)*x 0 + (-176252321/1000000000 : ℝ)*x 1 + (271601347/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647483241/5000000000 : ℝ)^4523 ≤ (43959261957351/100000000000000 : ℝ)^3499 := by
    have hnat : (2647483241 : ℕ)^4523*100000000000000^3499 ≤ 43959261957351^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647483241 5000000000 43959261957351 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176252321/1000000000 : ℝ)^4523 ≤ (1060504228159/10000000000000 : ℝ)^3499 := by
    have hnat : (176252321 : ℕ)^4523*10000000000000^3499 ≤ 1060504228159^3499*1000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176252321 1000000000 1060504228159 10000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271601347/500000000 : ℝ)^4523 ≤ (45435695746029/100000000000000 : ℝ)^3499 := by
    have hnat : (271601347 : ℕ)^4523*100000000000000^3499 ≤ 45435695746029^3499*500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271601347 500000000 45435695746029 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647483241/5000000000 : ℝ), (-176252321/1000000000 : ℝ), (271601347/500000000 : ℝ)] ![(43959261957351/100000000000000 : ℝ), (1060504228159/10000000000000 : ℝ), (45435695746029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647483241/5000000000 : ℝ)|^4523 ≤ (43959261957351/100000000000000 : ℝ)^3499
        have hw : |(2647483241/5000000000 : ℝ)|=(2647483241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176252321/1000000000 : ℝ)|^4523 ≤ (1060504228159/10000000000000 : ℝ)^3499
        have hw : |(-176252321/1000000000 : ℝ)|=(176252321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271601347/500000000 : ℝ)|^4523 ≤ (45435695746029/100000000000000 : ℝ)^3499
        have hw : |(271601347/500000000 : ℝ)|=(271601347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s5_6 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058993343/2000000000 : ℝ)*x 0 + (679003311/1250000000 : ℝ)*x 1 + (-1762523517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058993343/2000000000 : ℝ)^4523 ≤ (10989816114461/25000000000000 : ℝ)^3499 := by
    have hnat : (1058993343 : ℕ)^4523*25000000000000^3499 ≤ 10989816114461^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058993343 2000000000 10989816114461 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679003311/1250000000 : ℝ)^4523 ≤ (5679461357359/12500000000000 : ℝ)^3499 := by
    have hnat : (679003311 : ℕ)^4523*12500000000000^3499 ≤ 5679461357359^3499*1250000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679003311 1250000000 5679461357359 12500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1762523517/10000000000 : ℝ)^4523 ≤ (10605044669393/100000000000000 : ℝ)^3499 := by
    have hnat : (1762523517 : ℕ)^4523*100000000000000^3499 ≤ 10605044669393^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762523517 10000000000 10605044669393 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058993343/2000000000 : ℝ), (679003311/1250000000 : ℝ), (-1762523517/10000000000 : ℝ)] ![(10989816114461/25000000000000 : ℝ), (5679461357359/12500000000000 : ℝ), (10605044669393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058993343/2000000000 : ℝ)|^4523 ≤ (10989816114461/25000000000000 : ℝ)^3499
        have hw : |(1058993343/2000000000 : ℝ)|=(1058993343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679003311/1250000000 : ℝ)|^4523 ≤ (5679461357359/12500000000000 : ℝ)^3499
        have hw : |(679003311/1250000000 : ℝ)|=(679003311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1762523517/10000000000 : ℝ)|^4523 ≤ (10605044669393/100000000000000 : ℝ)^3499
        have hw : |(-1762523517/10000000000 : ℝ)|=(1762523517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s5_7 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4269368593/10000000000 : ℝ)*x 0 + (4517223651/10000000000 : ℝ)*x 1 + (4033278721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269368593/10000000000 : ℝ)^4523 ≤ (2080021031267/6250000000000 : ℝ)^3499 := by
    have hnat : (4269368593 : ℕ)^4523*6250000000000^3499 ≤ 2080021031267^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269368593 10000000000 2080021031267 6250000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517223651/10000000000 : ℝ)^4523 ≤ (4474845416289/12500000000000 : ℝ)^3499 := by
    have hnat : (4517223651 : ℕ)^4523*12500000000000^3499 ≤ 4474845416289^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517223651 10000000000 4474845416289 12500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033278721/10000000000 : ℝ)^4523 ≤ (30920900156133/100000000000000 : ℝ)^3499 := by
    have hnat : (4033278721 : ℕ)^4523*100000000000000^3499 ≤ 30920900156133^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033278721 10000000000 30920900156133 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269368593/10000000000 : ℝ), (4517223651/10000000000 : ℝ), (4033278721/10000000000 : ℝ)] ![(2080021031267/6250000000000 : ℝ), (4474845416289/12500000000000 : ℝ), (30920900156133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269368593/10000000000 : ℝ)|^4523 ≤ (2080021031267/6250000000000 : ℝ)^3499
        have hw : |(4269368593/10000000000 : ℝ)|=(4269368593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517223651/10000000000 : ℝ)|^4523 ≤ (4474845416289/12500000000000 : ℝ)^3499
        have hw : |(4517223651/10000000000 : ℝ)|=(4517223651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033278721/10000000000 : ℝ)|^4523 ≤ (30920900156133/100000000000000 : ℝ)^3499
        have hw : |(4033278721/10000000000 : ℝ)|=(4033278721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1513_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (341/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10919/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (341/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (341/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (341/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (341/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (341/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (341/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (341/3125 : ℝ) ^ (4521/1024 : ℝ) ≤ (1130681148412177/20000000000000000000 : ℝ) := by
    have hpowers : (341/3125 : ℝ)^4521 ≤ (1130681148412177/20000000000000000000 : ℝ)^1024 := by
      have hnat : (341 : ℕ)^4521*20000000000000000000^1024 ≤ 1130681148412177^1024*3125^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        341 3125 1130681148412177 20000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (341/3125 : ℝ)) (X := (1130681148412177/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4521/1024 : ℝ) ≤ (26548829033857067/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4521 ≤ (26548829033857067/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4521*100000000000000000000^1024 ≤ 26548829033857067^1024*10000^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 26548829033857067 100000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (26548829033857067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001130681148412177/10000000000000000000 : ℝ) ≤ (2000051217291261/2000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (10001130681148412177/10000000000000000000 : ℝ)^1024 ≤ (2000051217291261/2000000000000000 : ℝ)^4521 := by
      have hnat : (10001130681148412177 : ℕ)^1024*2000000000000000^4521 ≤ 2000051217291261^4521*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001130681148412177 10000000000000000000 2000051217291261 2000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000051217291261/2000000000000000 : ℝ)) (X := (10001130681148412177/10000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (781501579959186859/781250000000000000 : ℝ) ≤ (5000364642583459/5000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (781501579959186859/781250000000000000 : ℝ)^1024 ≤ (5000364642583459/5000000000000000 : ℝ)^4521 := by
      have hnat : (781501579959186859 : ℕ)^1024*5000000000000000^4521 ≤ 5000364642583459^4521*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781501579959186859 781250000000000000 5000364642583459 5000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000364642583459/5000000000000000 : ℝ)) (X := (781501579959186859/781250000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026548829033857067/50000000000000000000 : ℝ) ≤ (10001202483877531/10000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (50026548829033857067/50000000000000000000 : ℝ)^1024 ≤ (10001202483877531/10000000000000000 : ℝ)^4521 := by
      have hnat : (50026548829033857067 : ℕ)^1024*10000000000000000^4521 ≤ 10001202483877531^4521*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026548829033857067 50000000000000000000 10001202483877531 10000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001202483877531/10000000000000000 : ℝ)) (X := (50026548829033857067/50000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1130681148412177/20000000000000000000 : ℝ) ≤ ((22885422637568273089/22890000000000000000 : ℝ)+2*(473198710613/457800000000000 : ℝ)*(341/3125 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (22885422637568273089/22890000000000000000 : ℝ)+2*(473198710613/457800000000000 : ℝ)*(341/3125 : ℝ)=(2000051217291261/2000000000000000 : ℝ) by norm_num, show 1+2*(1130681148412177/20000000000000000000 : ℝ)=(10001130681148412177/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26548829033857067/100000000000000000000 : ℝ)+(1130681148412177/20000000000000000000 : ℝ) ≤ ((22885422637568273089/22890000000000000000 : ℝ)+(473198710613/457800000000000 : ℝ)*((1549/10000 : ℝ)+(341/3125 : ℝ)))^(4521/1024 : ℝ) := by
    rw [show (22885422637568273089/22890000000000000000 : ℝ)+(473198710613/457800000000000 : ℝ)*((1549/10000 : ℝ)+(341/3125 : ℝ))=(5000364642583459/5000000000000000 : ℝ) by norm_num, show 1+(26548829033857067/100000000000000000000 : ℝ)+(1130681148412177/20000000000000000000 : ℝ)=(781501579959186859/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26548829033857067/100000000000000000000 : ℝ) ≤ ((22885422637568273089/22890000000000000000 : ℝ)+2*(473198710613/457800000000000 : ℝ)*(1549/10000 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (22885422637568273089/22890000000000000000 : ℝ)+2*(473198710613/457800000000000 : ℝ)*(1549/10000 : ℝ)=(10001202483877531/10000000000000000 : ℝ) by norm_num, show 1+2*(26548829033857067/100000000000000000000 : ℝ)=(50026548829033857067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22885422637568273089/22890000000000000000 : ℝ)*(X 1 0+X 2 0)+(473198710613/457800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (341/3125 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (22885422637568273089/22890000000000000000 : ℝ)) (alpha := (473198710613/457800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22885422637568273089/22890000000000000000 : ℝ)*(X 0 1+X 2 1)+(473198710613/457800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (341/3125 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (22885422637568273089/22890000000000000000 : ℝ)) (alpha := (473198710613/457800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22885422637568273089/22890000000000000000 : ℝ)*(X 0 2+X 1 2)+(473198710613/457800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (341/3125 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (22885422637568273089/22890000000000000000 : ℝ)) (alpha := (473198710613/457800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-933267867/5000000000 : ℝ)*X 0 0+(5433144737/10000000000 : ℝ)*X 0 1+(5217648911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675772771/5000000000 : ℝ)*X 1 0+(-395380183/2000000000 : ℝ)*X 1 1+(1043529801/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351545567/10000000000 : ℝ)*X 2 0+(1304412241/2500000000 : ℝ)*X 2 1+(-1976900937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4269302819/10000000000 : ℝ)*X 0 0+(4030742279/10000000000 : ℝ)*X 0 1+(2259870811/5000000000 : ℝ)*X 0 2+(4269302819/10000000000 : ℝ)*X 1 0+(4030742279/10000000000 : ℝ)*X 1 1+(2259870811/5000000000 : ℝ)*X 1 2+(4269302819/10000000000 : ℝ)*X 2 0+(4030742279/10000000000 : ℝ)*X 2 1+(2259870811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1866564349/10000000000 : ℝ)*X 0 0+(1304689903/2500000000 : ℝ)*X 0 1+(1086405223/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647483241/5000000000 : ℝ)*X 1 0+(-176252321/1000000000 : ℝ)*X 1 1+(271601347/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058993343/2000000000 : ℝ)*X 2 0+(679003311/1250000000 : ℝ)*X 2 1+(-1762523517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4269368593/10000000000 : ℝ)*X 0 0+(4517223651/10000000000 : ℝ)*X 0 1+(4033278721/10000000000 : ℝ)*X 0 2+(4269368593/10000000000 : ℝ)*X 1 0+(4517223651/10000000000 : ℝ)*X 1 1+(4033278721/10000000000 : ℝ)*X 1 2+(4269368593/10000000000 : ℝ)*X 2 0+(4517223651/10000000000 : ℝ)*X 2 1+(4033278721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2527426342008841431553923399/381500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116547597/10000000000000 : ℝ)*(base19) + (223996793/20000000000000 : ℝ)*(base23) + (17973251/50000000000000 : ℝ)*(lower2) + (187794481/100000000000000 : ℝ)*(upper3) + (121456939/100000000000000 : ℝ)*(upper5) + (334275514544693/10000000000000 : ℝ)*(major0) + (334275514544693/10000000000000 : ℝ)*(major1) + (3342755145446931/100000000000000 : ℝ)*(major2) + (290030085700359/6250000000000 : ℝ)*(sp0) + (2320249740030901/50000000000000 : ℝ)*(sp1) + (4640499525553807/100000000000000 : ℝ)*(sp2) + (2045000445209703/100000000000000 : ℝ)*(sp3) + (4818583007/25000000000000 : ℝ)*(sp4) + (4489657009/50000000000000 : ℝ)*(sp7) + (2045009424523721/100000000000000 : ℝ)*(f.failure) + (1160125161384443/25000000000000 : ℝ)*(f.sum) + (28639515809621/6540000000000000000000000000 : ℝ)*base66 + (3135939400505918323/228900000000000000000000000000000 : ℝ)*base68 + (14916055810502560141/2289000000000000000000000000000000 : ℝ)*base70 + (2113049574710318323/228900000000000000000000000000000 : ℝ)*base72 + (16904648768899/6540000000000000000000000000 : ℝ)*base73 + (29401651263236560141/2289000000000000000000000000000000 : ℝ)*base76 + (455671070177126189/32700000000000000000000000000000 : ℝ)*base78 + (620252321935226189/32700000000000000000000000000000 : ℝ)*base80 + (40712301061/572250000000000000000000000 : ℝ)*base81 + (34159869/2500000000000000000000 : ℝ)*base89 + (34159869/2500000000000000000000 : ℝ)*base91 + (9159869/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3773269569566796430271109533/381500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (724467947/100000000000000 : ℝ)*(base19) + (723798277/50000000000000 : ℝ)*(base23) + (417479129/100000000000000 : ℝ)*(lower1) + (9384163/3125000000000 : ℝ)*(upper3) + (230020471/100000000000000 : ℝ)*(lower4) + (1688823180712299/50000000000000 : ℝ)*(major0) + (1688823180712299/50000000000000 : ℝ)*(major1) + (3377646361424599/100000000000000 : ℝ)*(major2) + (3854929511/50000000000000 : ℝ)*(sp2) + (1282535041/25000000000000 : ℝ)*(sp3) + (293058590190347/6250000000000 : ℝ)*(sp4) + (937787343715521/20000000000000 : ℝ)*(sp5) + (586116035698747/12500000000000 : ℝ)*(sp6) + (129146863748519/6250000000000 : ℝ)*(sp7) + (516588737529117/25000000000000 : ℝ)*(f.failure) + (293058590190347/6250000000000 : ℝ)*(f.sum) + (115471235085439/45780000000000000000000000000 : ℝ)*base66 + (18762910615835303389/1144500000000000000000000000000000 : ℝ)*base68 + (16350864261964983689/2289000000000000000000000000000000 : ℝ)*base70 + (26429655987008303389/1144500000000000000000000000000000 : ℝ)*base72 + (24865950841961/45780000000000000000000000000 : ℝ)*base73 + (28350004197544983689/2289000000000000000000000000000000 : ℝ)*base76 + (3071018223166744209/54500000000000000000000000000000 : ℝ)*base78 + (195431087990255791/54500000000000000000000000000000 : ℝ)*base79 + (43756870630161/3815000000000000000000000000 : ℝ)*base82 + (10061313/625000000000000000000 : ℝ)*base89 + (10061313/625000000000000000000 : ℝ)*base91 + (3811313/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1513_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (341/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1513_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1513_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (209/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1513_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1513_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1513_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (209/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1513_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
