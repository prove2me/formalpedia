-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1390_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:39.707802+00:00
-- url     : https://prove2.me/submissions/6abfa2f4-5f52-4891-8035-7349b77bc5cf

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
theorem support_rectangle_w1390_s3_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-100094559/500000000 : ℝ)*x 0 + (5421423757/10000000000 : ℝ)*x 1 + (1047129217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100094559/500000000 : ℝ)^2175 ≤ (12200280672897/100000000000000 : ℝ)^1663 := by
    have hnat : (100094559 : ℕ)^2175*100000000000000^1663 ≤ 12200280672897^1663*500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100094559 500000000 12200280672897 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421423757/10000000000 : ℝ)^2175 ≤ (22450338231427/50000000000000 : ℝ)^1663 := by
    have hnat : (5421423757 : ℕ)^2175*50000000000000^1663 ≤ 22450338231427^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421423757 10000000000 22450338231427 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047129217/2000000000 : ℝ)^2175 ≤ (42899042849947/100000000000000 : ℝ)^1663 := by
    have hnat : (1047129217 : ℕ)^2175*100000000000000^1663 ≤ 42899042849947^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047129217 2000000000 42899042849947 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100094559/500000000 : ℝ), (5421423757/10000000000 : ℝ), (1047129217/2000000000 : ℝ)] ![(12200280672897/100000000000000 : ℝ), (22450338231427/50000000000000 : ℝ), (42899042849947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100094559/500000000 : ℝ)|^2175 ≤ (12200280672897/100000000000000 : ℝ)^1663
        have hw : |(-100094559/500000000 : ℝ)|=(100094559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421423757/10000000000 : ℝ)|^2175 ≤ (22450338231427/50000000000000 : ℝ)^1663
        have hw : |(5421423757/10000000000 : ℝ)|=(5421423757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047129217/2000000000 : ℝ)|^2175 ≤ (42899042849947/100000000000000 : ℝ)^1663
        have hw : |(1047129217/2000000000 : ℝ)|=(1047129217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s3_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214039649/400000000 : ℝ)*x 0 + (-419346117/2000000000 : ℝ)*x 1 + (2617823089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214039649/400000000 : ℝ)^2175 ≤ (2206964267269/5000000000000 : ℝ)^1663 := by
    have hnat : (214039649 : ℕ)^2175*5000000000000^1663 ≤ 2206964267269^1663*400000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214039649 400000000 2206964267269 5000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419346117/2000000000 : ℝ)^2175 ≤ (1620208848649/12500000000000 : ℝ)^1663 := by
    have hnat : (419346117 : ℕ)^2175*12500000000000^1663 ≤ 1620208848649^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419346117 2000000000 1620208848649 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617823089/5000000000 : ℝ)^2175 ≤ (21449521923281/50000000000000 : ℝ)^1663 := by
    have hnat : (2617823089 : ℕ)^2175*50000000000000^1663 ≤ 21449521923281^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617823089 5000000000 21449521923281 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214039649/400000000 : ℝ), (-419346117/2000000000 : ℝ), (2617823089/5000000000 : ℝ)] ![(2206964267269/5000000000000 : ℝ), (1620208848649/12500000000000 : ℝ), (21449521923281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214039649/400000000 : ℝ)|^2175 ≤ (2206964267269/5000000000000 : ℝ)^1663
        have hw : |(214039649/400000000 : ℝ)|=(214039649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419346117/2000000000 : ℝ)|^2175 ≤ (1620208848649/12500000000000 : ℝ)^1663
        have hw : |(-419346117/2000000000 : ℝ)|=(419346117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617823089/5000000000 : ℝ)|^2175 ≤ (21449521923281/50000000000000 : ℝ)^1663
        have hw : |(2617823089/5000000000 : ℝ)|=(2617823089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s3_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070198249/2000000000 : ℝ)*x 0 + (523564617/1000000000 : ℝ)*x 1 + (-2096730569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070198249/2000000000 : ℝ)^2175 ≤ (44139285561149/100000000000000 : ℝ)^1663 := by
    have hnat : (1070198249 : ℕ)^2175*100000000000000^1663 ≤ 44139285561149^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070198249 2000000000 44139285561149 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523564617/1000000000 : ℝ)^2175 ≤ (670297558763/1562500000000 : ℝ)^1663 := by
    have hnat : (523564617 : ℕ)^2175*1562500000000^1663 ≤ 670297558763^1663*1000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523564617 1000000000 670297558763 1562500000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096730569/10000000000 : ℝ)^2175 ≤ (1296167065983/10000000000000 : ℝ)^1663 := by
    have hnat : (2096730569 : ℕ)^2175*10000000000000^1663 ≤ 1296167065983^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096730569 10000000000 1296167065983 10000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070198249/2000000000 : ℝ), (523564617/1000000000 : ℝ), (-2096730569/10000000000 : ℝ)] ![(44139285561149/100000000000000 : ℝ), (670297558763/1562500000000 : ℝ), (1296167065983/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070198249/2000000000 : ℝ)|^2175 ≤ (44139285561149/100000000000000 : ℝ)^1663
        have hw : |(1070198249/2000000000 : ℝ)|=(1070198249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523564617/1000000000 : ℝ)|^2175 ≤ (670297558763/1562500000000 : ℝ)^1663
        have hw : |(523564617/1000000000 : ℝ)|=(523564617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096730569/10000000000 : ℝ)|^2175 ≤ (1296167065983/10000000000000 : ℝ)^1663
        have hw : |(-2096730569/10000000000 : ℝ)|=(2096730569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s3_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1078353673/2500000000 : ℝ)*x 0 + (823898569/2000000000 : ℝ)*x 1 + (2257827687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078353673/2500000000 : ℝ)^2175 ≤ (416198927151/1250000000000 : ℝ)^1663 := by
    have hnat : (1078353673 : ℕ)^2175*1250000000000^1663 ≤ 416198927151^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078353673 2500000000 416198927151 1250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (823898569/2000000000 : ℝ)^2175 ≤ (15675914287201/50000000000000 : ℝ)^1663 := by
    have hnat : (823898569 : ℕ)^2175*50000000000000^1663 ≤ 15675914287201^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823898569 2000000000 15675914287201 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257827687/5000000000 : ℝ)^2175 ≤ (7070451447843/20000000000000 : ℝ)^1663 := by
    have hnat : (2257827687 : ℕ)^2175*20000000000000^1663 ≤ 7070451447843^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257827687 5000000000 7070451447843 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078353673/2500000000 : ℝ), (823898569/2000000000 : ℝ), (2257827687/5000000000 : ℝ)] ![(416198927151/1250000000000 : ℝ), (15675914287201/50000000000000 : ℝ), (7070451447843/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078353673/2500000000 : ℝ)|^2175 ≤ (416198927151/1250000000000 : ℝ)^1663
        have hw : |(1078353673/2500000000 : ℝ)|=(1078353673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(823898569/2000000000 : ℝ)|^2175 ≤ (15675914287201/50000000000000 : ℝ)^1663
        have hw : |(823898569/2000000000 : ℝ)|=(823898569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257827687/5000000000 : ℝ)|^2175 ≤ (7070451447843/20000000000000 : ℝ)^1663
        have hw : |(2257827687/5000000000 : ℝ)|=(2257827687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s3_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001908261/10000000000 : ℝ)*x 0 + (2618200371/5000000000 : ℝ)*x 1 + (1355166139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001908261/10000000000 : ℝ)^2175 ≤ (3050104205143/25000000000000 : ℝ)^1663 := by
    have hnat : (2001908261 : ℕ)^2175*25000000000000^1663 ≤ 3050104205143^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001908261 10000000000 3050104205143 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618200371/5000000000 : ℝ)^2175 ≤ (10726782537579/25000000000000 : ℝ)^1663 := by
    have hnat : (2618200371 : ℕ)^2175*25000000000000^1663 ≤ 10726782537579^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618200371 5000000000 10726782537579 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355166139/2500000000 : ℝ)^2175 ≤ (5611556626857/12500000000000 : ℝ)^1663 := by
    have hnat : (1355166139 : ℕ)^2175*12500000000000^1663 ≤ 5611556626857^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355166139 2500000000 5611556626857 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001908261/10000000000 : ℝ), (2618200371/5000000000 : ℝ), (1355166139/2500000000 : ℝ)] ![(3050104205143/25000000000000 : ℝ), (10726782537579/25000000000000 : ℝ), (5611556626857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001908261/10000000000 : ℝ)|^2175 ≤ (3050104205143/25000000000000 : ℝ)^1663
        have hw : |(-2001908261/10000000000 : ℝ)|=(2001908261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618200371/5000000000 : ℝ)|^2175 ≤ (10726782537579/25000000000000 : ℝ)^1663
        have hw : |(2618200371/5000000000 : ℝ)|=(2618200371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355166139/2500000000 : ℝ)|^2175 ≤ (5611556626857/12500000000000 : ℝ)^1663
        have hw : |(1355166139/2500000000 : ℝ)|=(1355166139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s3_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302885363/10000000000 : ℝ)*x 0 + (-955856107/5000000000 : ℝ)*x 1 + (5420664541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302885363/10000000000 : ℝ)^2175 ≤ (21810509282343/50000000000000 : ℝ)^1663 := by
    have hnat : (5302885363 : ℕ)^2175*50000000000000^1663 ≤ 21810509282343^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302885363 10000000000 21810509282343 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955856107/5000000000 : ℝ)^2175 ≤ (2871632143543/25000000000000 : ℝ)^1663 := by
    have hnat : (955856107 : ℕ)^2175*25000000000000^1663 ≤ 2871632143543^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955856107 5000000000 2871632143543 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420664541/10000000000 : ℝ)^2175 ≤ (1402889151637/3125000000000 : ℝ)^1663 := by
    have hnat : (5420664541 : ℕ)^2175*3125000000000^1663 ≤ 1402889151637^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420664541 10000000000 1402889151637 3125000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302885363/10000000000 : ℝ), (-955856107/5000000000 : ℝ), (5420664541/10000000000 : ℝ)] ![(21810509282343/50000000000000 : ℝ), (2871632143543/25000000000000 : ℝ), (1402889151637/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302885363/10000000000 : ℝ)|^2175 ≤ (21810509282343/50000000000000 : ℝ)^1663
        have hw : |(5302885363/10000000000 : ℝ)|=(5302885363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-955856107/5000000000 : ℝ)|^2175 ≤ (2871632143543/25000000000000 : ℝ)^1663
        have hw : |(-955856107/5000000000 : ℝ)|=(955856107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420664541/10000000000 : ℝ)|^2175 ≤ (1402889151637/3125000000000 : ℝ)^1663
        have hw : |(5420664541/10000000000 : ℝ)|=(5420664541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s3_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265144273/500000000 : ℝ)*x 0 + (5420664453/10000000000 : ℝ)*x 1 + (-955856101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265144273/500000000 : ℝ)^2175 ≤ (43621019608257/100000000000000 : ℝ)^1663 := by
    have hnat : (265144273 : ℕ)^2175*100000000000000^1663 ≤ 43621019608257^1663*500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265144273 500000000 43621019608257 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420664453/10000000000 : ℝ)^2175 ≤ (22446225949607/50000000000000 : ℝ)^1663 := by
    have hnat : (5420664453 : ℕ)^2175*50000000000000^1663 ≤ 22446225949607^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420664453 10000000000 22446225949607 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955856101/5000000000 : ℝ)^2175 ≤ (89738503749/781250000000 : ℝ)^1663 := by
    have hnat : (955856101 : ℕ)^2175*781250000000^1663 ≤ 89738503749^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955856101 5000000000 89738503749 781250000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265144273/500000000 : ℝ), (5420664453/10000000000 : ℝ), (-955856101/5000000000 : ℝ)] ![(43621019608257/100000000000000 : ℝ), (22446225949607/50000000000000 : ℝ), (89738503749/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265144273/500000000 : ℝ)|^2175 ≤ (43621019608257/100000000000000 : ℝ)^1663
        have hw : |(265144273/500000000 : ℝ)|=(265144273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420664453/10000000000 : ℝ)|^2175 ≤ (22446225949607/50000000000000 : ℝ)^1663
        have hw : |(5420664453/10000000000 : ℝ)|=(5420664453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-955856101/5000000000 : ℝ)|^2175 ≤ (89738503749/781250000000 : ℝ)^1663
        have hw : |(-955856101/5000000000 : ℝ)|=(955856101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s3_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4313450731/10000000000 : ℝ)*x 0 + (282127909/625000000 : ℝ)*x 1 + (4121111063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313450731/10000000000 : ℝ)^2175 ≤ (4162034751467/12500000000000 : ℝ)^1663 := by
    have hnat : (4313450731 : ℕ)^2175*12500000000000^1663 ≤ 4162034751467^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313450731 10000000000 4162034751467 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282127909/625000000 : ℝ)^2175 ≤ (7067157022267/20000000000000 : ℝ)^1663 := by
    have hnat : (282127909 : ℕ)^2175*20000000000000^1663 ≤ 7067157022267^1663*625000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282127909 625000000 7067157022267 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4121111063/10000000000 : ℝ)^2175 ≤ (31367936863723/100000000000000 : ℝ)^1663 := by
    have hnat : (4121111063 : ℕ)^2175*100000000000000^1663 ≤ 31367936863723^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121111063 10000000000 31367936863723 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313450731/10000000000 : ℝ), (282127909/625000000 : ℝ), (4121111063/10000000000 : ℝ)] ![(4162034751467/12500000000000 : ℝ), (7067157022267/20000000000000 : ℝ), (31367936863723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313450731/10000000000 : ℝ)|^2175 ≤ (4162034751467/12500000000000 : ℝ)^1663
        have hw : |(4313450731/10000000000 : ℝ)|=(4313450731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282127909/625000000 : ℝ)|^2175 ≤ (7067157022267/20000000000000 : ℝ)^1663
        have hw : |(282127909/625000000 : ℝ)|=(282127909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4121111063/10000000000 : ℝ)|^2175 ≤ (31367936863723/100000000000000 : ℝ)^1663
        have hw : |(4121111063/10000000000 : ℝ)|=(4121111063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7963/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11037/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1497/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7963/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7963/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7963/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7963/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7963/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7963/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10149/100000 : ℝ) ^ (4349/1024 : ℝ) ≤ (6028505931233699/100000000000000000000 : ℝ) := by
    have hpowers : (10149/100000 : ℝ)^4349 ≤ (6028505931233699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10149 : ℕ)^4349*100000000000000000000^1024 ≤ 6028505931233699^1024*100000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10149 100000 6028505931233699 100000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10149/100000 : ℝ)) (X := (6028505931233699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7963/50000 : ℝ) ^ (4349/1024 : ℝ) ≤ (20429658437236519/50000000000000000000 : ℝ) := by
    have hpowers : (7963/50000 : ℝ)^4349 ≤ (20429658437236519/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7963 : ℕ)^4349*50000000000000000000^1024 ≤ 20429658437236519^1024*50000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7963 50000 20429658437236519 50000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7963/50000 : ℝ)) (X := (20429658437236519/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006028505931233699/50000000000000000000 : ℝ) ≤ (1250035484626167/1250000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (50006028505931233699/50000000000000000000 : ℝ)^1024 ≤ (1250035484626167/1250000000000000 : ℝ)^4349 := by
      have hnat : (50006028505931233699 : ℕ)^1024*1250000000000000^4349 ≤ 1250035484626167^4349*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006028505931233699 50000000000000000000 1250035484626167 1250000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035484626167/1250000000000000 : ℝ)) (X := (50006028505931233699/50000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046887822805706737/100000000000000000000 : ℝ) ≤ (2500275951523937/2500000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (100046887822805706737/100000000000000000000 : ℝ)^1024 ≤ (2500275951523937/2500000000000000 : ℝ)^4349 := by
      have hnat : (100046887822805706737 : ℕ)^1024*2500000000000000^4349 ≤ 2500275951523937^4349*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046887822805706737 100000000000000000000 2500275951523937 2500000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500275951523937/2500000000000000 : ℝ)) (X := (100046887822805706737/100000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020429658437236519/25000000000000000000 : ℝ) ≤ (125024046689777/125000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (25020429658437236519/25000000000000000000 : ℝ)^1024 ≤ (125024046689777/125000000000000 : ℝ)^4349 := by
      have hnat : (25020429658437236519 : ℕ)^1024*125000000000000^4349 ≤ 125024046689777^4349*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020429658437236519 25000000000000000000 125024046689777 125000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125024046689777/125000000000000 : ℝ)) (X := (25020429658437236519/25000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6028505931233699/100000000000000000000 : ℝ) ≤ ((902421828701358489/902656250000000000 : ℝ)+2*(204982271603/144425000000000 : ℝ)*(10149/100000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (902421828701358489/902656250000000000 : ℝ)+2*(204982271603/144425000000000 : ℝ)*(10149/100000 : ℝ)=(1250035484626167/1250000000000000 : ℝ) by norm_num, show 1+2*(6028505931233699/100000000000000000000 : ℝ)=(50006028505931233699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20429658437236519/50000000000000000000 : ℝ)+(6028505931233699/100000000000000000000 : ℝ) ≤ ((902421828701358489/902656250000000000 : ℝ)+(204982271603/144425000000000 : ℝ)*((7963/50000 : ℝ)+(10149/100000 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (902421828701358489/902656250000000000 : ℝ)+(204982271603/144425000000000 : ℝ)*((7963/50000 : ℝ)+(10149/100000 : ℝ))=(2500275951523937/2500000000000000 : ℝ) by norm_num, show 1+(20429658437236519/50000000000000000000 : ℝ)+(6028505931233699/100000000000000000000 : ℝ)=(100046887822805706737/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20429658437236519/50000000000000000000 : ℝ) ≤ ((902421828701358489/902656250000000000 : ℝ)+2*(204982271603/144425000000000 : ℝ)*(7963/50000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (902421828701358489/902656250000000000 : ℝ)+2*(204982271603/144425000000000 : ℝ)*(7963/50000 : ℝ)=(125024046689777/125000000000000 : ℝ) by norm_num, show 1+2*(20429658437236519/50000000000000000000 : ℝ)=(25020429658437236519/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (902421828701358489/902656250000000000 : ℝ)*(X 1 0+X 2 0)+(204982271603/144425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (10149/100000 : ℝ)) (hi := (7963/50000 : ℝ)) (c := (902421828701358489/902656250000000000 : ℝ)) (alpha := (204982271603/144425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (902421828701358489/902656250000000000 : ℝ)*(X 0 1+X 2 1)+(204982271603/144425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (10149/100000 : ℝ)) (hi := (7963/50000 : ℝ)) (c := (902421828701358489/902656250000000000 : ℝ)) (alpha := (204982271603/144425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (902421828701358489/902656250000000000 : ℝ)*(X 0 2+X 1 2)+(204982271603/144425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (10149/100000 : ℝ)) (hi := (7963/50000 : ℝ)) (c := (902421828701358489/902656250000000000 : ℝ)) (alpha := (204982271603/144425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-100094559/500000000 : ℝ)*X 0 0+(5421423757/10000000000 : ℝ)*X 0 1+(1047129217/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214039649/400000000 : ℝ)*X 1 0+(-419346117/2000000000 : ℝ)*X 1 1+(2617823089/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070198249/2000000000 : ℝ)*X 2 0+(523564617/1000000000 : ℝ)*X 2 1+(-2096730569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078353673/2500000000 : ℝ)*X 0 0+(823898569/2000000000 : ℝ)*X 0 1+(2257827687/5000000000 : ℝ)*X 0 2+(1078353673/2500000000 : ℝ)*X 1 0+(823898569/2000000000 : ℝ)*X 1 1+(2257827687/5000000000 : ℝ)*X 1 2+(1078353673/2500000000 : ℝ)*X 2 0+(823898569/2000000000 : ℝ)*X 2 1+(2257827687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2001908261/10000000000 : ℝ)*X 0 0+(2618200371/5000000000 : ℝ)*X 0 1+(1355166139/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302885363/10000000000 : ℝ)*X 1 0+(-955856107/5000000000 : ℝ)*X 1 1+(5420664541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265144273/500000000 : ℝ)*X 2 0+(5420664453/10000000000 : ℝ)*X 2 1+(-955856101/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313450731/10000000000 : ℝ)*X 0 0+(282127909/625000000 : ℝ)*X 0 1+(4121111063/10000000000 : ℝ)*X 0 2+(4313450731/10000000000 : ℝ)*X 1 0+(282127909/625000000 : ℝ)*X 1 1+(4121111063/10000000000 : ℝ)*X 1 2+(4313450731/10000000000 : ℝ)*X 2 0+(282127909/625000000 : ℝ)*X 2 1+(4121111063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (830934967648690619847731271/90265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1491548947/100000000000000 : ℝ)*(base19) + (9771973/781250000000 : ℝ)*(base23) + (139583509/100000000000000 : ℝ)*(lower2) + (58535403/25000000000000 : ℝ)*(upper3) + (59654047/100000000000000 : ℝ)*(upper5) + (1976768855616561/50000000000000 : ℝ)*(major0) + (1976768855616561/50000000000000 : ℝ)*(major1) + (1976768855616561/50000000000000 : ℝ)*(major2) + (5382809398308357/100000000000000 : ℝ)*(sp0) + (5382836365835347/100000000000000 : ℝ)*(sp1) + (5382836606571749/100000000000000 : ℝ)*(sp2) + (504845033123473/20000000000000 : ℝ)*(sp3) + (889346123/3125000000000 : ℝ)*(sp4) + (2418523303/20000000000000 : ℝ)*(sp7) + (63105931455847/2500000000000 : ℝ)*(f.failure) + (5382837857384293/100000000000000 : ℝ)*(f.sum) + (5113892836501/28885000000000000000000000000 : ℝ)*base66 + (35051384939705273/22566406250000000000000000000000 : ℝ)*base68 + (187941039656676171/45132812500000000000000000000000 : ℝ)*base70 + (7601486945019921/45132812500000000000000000000000 : ℝ)*base72 + (48511379759443/14442500000000000000000000000 : ℝ)*base74 + (1870707638655305467/90265625000000000000000000000000 : ℝ)*base76 + (191136696781391699/11283203125000000000000000000000 : ℝ)*base78 + (371973389926913283/90265625000000000000000000000000 : ℝ)*base79 + (81419991133137/14442500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1399361/250000000000000000000 : ℝ)*base89 + (1399361/250000000000000000000 : ℝ)*base91 + (1399361/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28844516027623351215737997/4513281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1117645801/100000000000000 : ℝ)*(base19) + (638781221/50000000000000 : ℝ)*(base23) + (144454531/100000000000000 : ℝ)*(upper3) + (23323953/100000000000000 : ℝ)*(lower4) + (135201631/100000000000000 : ℝ)*(upper5) + (49824681760509/1250000000000 : ℝ)*(major0) + (49824681760509/1250000000000 : ℝ)*(major1) + (49824681760509/1250000000000 : ℝ)*(major2) + (2426870401/12500000000000 : ℝ)*(sp1) + (10625900783/50000000000000 : ℝ)*(sp2) + (5427001487021231/100000000000000 : ℝ)*(sp4) + (2713490477206111/50000000000000 : ℝ)*(sp5) + (5426978957657223/100000000000000 : ℝ)*(sp6) + (127247369081293/5000000000000 : ℝ)*(sp7) + (127247369081293/5000000000000 : ℝ)*(f.failure) + (5427001487021231/100000000000000 : ℝ)*(f.sum) + (7549452950077/1155400000000000000000000000 : ℝ)*base66 + (129244973016503417/9026562500000000000000000000000 : ℝ)*base68 + (10391768064761737/564160156250000000000000000000 : ℝ)*base70 + (220069150908234667/9026562500000000000000000000000 : ℝ)*base72 + (10040826498569/1444250000000000000000000000 : ℝ)*base74 + (205687745030140917/9026562500000000000000000000000 : ℝ)*base76 + (144571080222809667/9026562500000000000000000000000 : ℝ)*base78 + (405163333437222459/18053125000000000000000000000000 : ℝ)*base80 + (1188566286729/722125000000000000000000000 : ℝ)*base82 + (5660459/500000000000000000000 : ℝ)*base89 + (5660459/500000000000000000000 : ℝ)*base91 + (5660459/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1390_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7963/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1497/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1390_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1390_s4_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-125188141/625000000 : ℝ)*x 0 + (5412049791/10000000000 : ℝ)*x 1 + (1311071019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125188141/625000000 : ℝ)^2175 ≤ (2441840251497/20000000000000 : ℝ)^1663 := by
    have hnat : (125188141 : ℕ)^2175*20000000000000^1663 ≤ 2441840251497^1663*625000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125188141 625000000 2441840251497 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412049791/10000000000 : ℝ)^2175 ≤ (1399973912299/3125000000000 : ℝ)^1663 := by
    have hnat : (5412049791 : ℕ)^2175*3125000000000^1663 ≤ 1399973912299^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412049791 10000000000 1399973912299 3125000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311071019/2500000000 : ℝ)^2175 ≤ (5373954192579/12500000000000 : ℝ)^1663 := by
    have hnat : (1311071019 : ℕ)^2175*12500000000000^1663 ≤ 5373954192579^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311071019 2500000000 5373954192579 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125188141/625000000 : ℝ), (5412049791/10000000000 : ℝ), (1311071019/2500000000 : ℝ)] ![(2441840251497/20000000000000 : ℝ), (1399973912299/3125000000000 : ℝ), (5373954192579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125188141/625000000 : ℝ)|^2175 ≤ (2441840251497/20000000000000 : ℝ)^1663
        have hw : |(-125188141/625000000 : ℝ)|=(125188141/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412049791/10000000000 : ℝ)|^2175 ≤ (1399973912299/3125000000000 : ℝ)^1663
        have hw : |(5412049791/10000000000 : ℝ)|=(5412049791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311071019/2500000000 : ℝ)|^2175 ≤ (5373954192579/12500000000000 : ℝ)^1663
        have hw : |(1311071019/2500000000 : ℝ)|=(1311071019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s4_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348585119/10000000000 : ℝ)*x 0 + (-1044242043/5000000000 : ℝ)*x 1 + (5244284073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348585119/10000000000 : ℝ)^2175 ≤ (22056664523413/50000000000000 : ℝ)^1663 := by
    have hnat : (5348585119 : ℕ)^2175*50000000000000^1663 ≤ 22056664523413^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348585119 10000000000 22056664523413 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044242043/5000000000 : ℝ)^2175 ≤ (12895037428311/100000000000000 : ℝ)^1663 := by
    have hnat : (1044242043 : ℕ)^2175*100000000000000^1663 ≤ 12895037428311^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044242043 5000000000 12895037428311 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244284073/10000000000 : ℝ)^2175 ≤ (42991633508467/100000000000000 : ℝ)^1663 := by
    have hnat : (5244284073 : ℕ)^2175*100000000000000^1663 ≤ 42991633508467^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244284073 10000000000 42991633508467 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348585119/10000000000 : ℝ), (-1044242043/5000000000 : ℝ), (5244284073/10000000000 : ℝ)] ![(22056664523413/50000000000000 : ℝ), (12895037428311/100000000000000 : ℝ), (42991633508467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348585119/10000000000 : ℝ)|^2175 ≤ (22056664523413/50000000000000 : ℝ)^1663
        have hw : |(5348585119/10000000000 : ℝ)|=(5348585119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044242043/5000000000 : ℝ)|^2175 ≤ (12895037428311/100000000000000 : ℝ)^1663
        have hw : |(-1044242043/5000000000 : ℝ)|=(1044242043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244284073/10000000000 : ℝ)|^2175 ≤ (42991633508467/100000000000000 : ℝ)^1663
        have hw : |(5244284073/10000000000 : ℝ)|=(5244284073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s4_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348585121/10000000000 : ℝ)*x 0 + (1311071017/2500000000 : ℝ)*x 1 + (-208848409/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348585121/10000000000 : ℝ)^2175 ≤ (110283322671/250000000000 : ℝ)^1663 := by
    have hnat : (5348585121 : ℕ)^2175*250000000000^1663 ≤ 110283322671^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348585121 10000000000 110283322671 250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311071017/2500000000 : ℝ)^2175 ≤ (21495816727429/50000000000000 : ℝ)^1663 := by
    have hnat : (1311071017 : ℕ)^2175*50000000000000^1663 ≤ 21495816727429^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311071017 2500000000 21495816727429 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208848409/1000000000 : ℝ)^2175 ≤ (3223759365153/25000000000000 : ℝ)^1663 := by
    have hnat : (208848409 : ℕ)^2175*25000000000000^1663 ≤ 3223759365153^1663*1000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208848409 1000000000 3223759365153 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348585121/10000000000 : ℝ), (1311071017/2500000000 : ℝ), (-208848409/1000000000 : ℝ)] ![(110283322671/250000000000 : ℝ), (21495816727429/50000000000000 : ℝ), (3223759365153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348585121/10000000000 : ℝ)|^2175 ≤ (110283322671/250000000000 : ℝ)^1663
        have hw : |(5348585121/10000000000 : ℝ)|=(5348585121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311071017/2500000000 : ℝ)|^2175 ≤ (21495816727429/50000000000000 : ℝ)^1663
        have hw : |(1311071017/2500000000 : ℝ)|=(1311071017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208848409/1000000000 : ℝ)|^2175 ≤ (3223759365153/25000000000000 : ℝ)^1663
        have hw : |(-208848409/1000000000 : ℝ)|=(208848409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s4_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (431409803/1000000000 : ℝ)*x 0 + (4138613779/10000000000 : ℝ)*x 1 + (281022979/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431409803/1000000000 : ℝ)^2175 ≤ (16651406560307/50000000000000 : ℝ)^1663 := by
    have hnat : (431409803 : ℕ)^2175*50000000000000^1663 ≤ 16651406560307^1663*1000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431409803 1000000000 16651406560307 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4138613779/10000000000 : ℝ)^2175 ≤ (6308457831219/20000000000000 : ℝ)^1663 := by
    have hnat : (4138613779 : ℕ)^2175*20000000000000^1663 ≤ 6308457831219^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138613779 10000000000 6308457831219 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281022979/625000000 : ℝ)^2175 ≤ (35154897707537/100000000000000 : ℝ)^1663 := by
    have hnat : (281022979 : ℕ)^2175*100000000000000^1663 ≤ 35154897707537^1663*625000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281022979 625000000 35154897707537 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431409803/1000000000 : ℝ), (4138613779/10000000000 : ℝ), (281022979/625000000 : ℝ)] ![(16651406560307/50000000000000 : ℝ), (6308457831219/20000000000000 : ℝ), (35154897707537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431409803/1000000000 : ℝ)|^2175 ≤ (16651406560307/50000000000000 : ℝ)^1663
        have hw : |(431409803/1000000000 : ℝ)|=(431409803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4138613779/10000000000 : ℝ)|^2175 ≤ (6308457831219/20000000000000 : ℝ)^1663
        have hw : |(4138613779/10000000000 : ℝ)|=(4138613779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281022979/625000000 : ℝ)|^2175 ≤ (35154897707537/100000000000000 : ℝ)^1663
        have hw : |(281022979/625000000 : ℝ)|=(281022979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s4_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003022781/10000000000 : ℝ)*x 0 + (524489981/1000000000 : ℝ)*x 1 + (169107211/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003022781/10000000000 : ℝ)^2175 ≤ (2441860221551/20000000000000 : ℝ)^1663 := by
    have hnat : (2003022781 : ℕ)^2175*20000000000000^1663 ≤ 2441860221551^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003022781 10000000000 2441860221551 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524489981/1000000000 : ℝ)^2175 ≤ (21499117695943/50000000000000 : ℝ)^1663 := by
    have hnat : (524489981 : ℕ)^2175*50000000000000^1663 ≤ 21499117695943^1663*1000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524489981 1000000000 21499117695943 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169107211/312500000 : ℝ)^2175 ≤ (2239623174269/5000000000000 : ℝ)^1663 := by
    have hnat : (169107211 : ℕ)^2175*5000000000000^1663 ≤ 2239623174269^1663*312500000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169107211 312500000 2239623174269 5000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003022781/10000000000 : ℝ), (524489981/1000000000 : ℝ), (169107211/312500000 : ℝ)] ![(2441860221551/20000000000000 : ℝ), (21499117695943/50000000000000 : ℝ), (2239623174269/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003022781/10000000000 : ℝ)|^2175 ≤ (2441860221551/20000000000000 : ℝ)^1663
        have hw : |(-2003022781/10000000000 : ℝ)|=(2003022781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524489981/1000000000 : ℝ)|^2175 ≤ (21499117695943/50000000000000 : ℝ)^1663
        have hw : |(524489981/1000000000 : ℝ)|=(524489981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169107211/312500000 : ℝ)|^2175 ≤ (2239623174269/5000000000000 : ℝ)^1663
        have hw : |(169107211/312500000 : ℝ)|=(169107211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s4_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326285783/2500000000 : ℝ)*x 0 + (-960668681/5000000000 : ℝ)*x 1 + (5411430841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326285783/2500000000 : ℝ)^2175 ≤ (10911327575021/25000000000000 : ℝ)^1663 := by
    have hnat : (1326285783 : ℕ)^2175*25000000000000^1663 ≤ 10911327575021^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326285783 2500000000 10911327575021 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960668681/5000000000 : ℝ)^2175 ≤ (5781112623639/50000000000000 : ℝ)^1663 := by
    have hnat : (960668681 : ℕ)^2175*50000000000000^1663 ≤ 5781112623639^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960668681 5000000000 5781112623639 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411430841/10000000000 : ℝ)^2175 ≤ (11198116112219/25000000000000 : ℝ)^1663 := by
    have hnat : (5411430841 : ℕ)^2175*25000000000000^1663 ≤ 11198116112219^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411430841 10000000000 11198116112219 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326285783/2500000000 : ℝ), (-960668681/5000000000 : ℝ), (5411430841/10000000000 : ℝ)] ![(10911327575021/25000000000000 : ℝ), (5781112623639/50000000000000 : ℝ), (11198116112219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326285783/2500000000 : ℝ)|^2175 ≤ (10911327575021/25000000000000 : ℝ)^1663
        have hw : |(1326285783/2500000000 : ℝ)|=(1326285783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960668681/5000000000 : ℝ)|^2175 ≤ (5781112623639/50000000000000 : ℝ)^1663
        have hw : |(-960668681/5000000000 : ℝ)|=(960668681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411430841/10000000000 : ℝ)|^2175 ≤ (11198116112219/25000000000000 : ℝ)^1663
        have hw : |(5411430841/10000000000 : ℝ)|=(5411430841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s4_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326285769/2500000000 : ℝ)*x 0 + (1082286163/2000000000 : ℝ)*x 1 + (-1921337473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326285769/2500000000 : ℝ)^2175 ≤ (43645309697531/100000000000000 : ℝ)^1663 := by
    have hnat : (1326285769 : ℕ)^2175*100000000000000^1663 ≤ 43645309697531^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326285769 2500000000 43645309697531 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082286163/2000000000 : ℝ)^2175 ≤ (8958492833481/20000000000000 : ℝ)^1663 := by
    have hnat : (1082286163 : ℕ)^2175*20000000000000^1663 ≤ 8958492833481^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082286163 2000000000 8958492833481 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921337473/10000000000 : ℝ)^2175 ≤ (2890556530227/25000000000000 : ℝ)^1663 := by
    have hnat : (1921337473 : ℕ)^2175*25000000000000^1663 ≤ 2890556530227^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921337473 10000000000 2890556530227 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326285769/2500000000 : ℝ), (1082286163/2000000000 : ℝ), (-1921337473/10000000000 : ℝ)] ![(43645309697531/100000000000000 : ℝ), (8958492833481/20000000000000 : ℝ), (2890556530227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326285769/2500000000 : ℝ)|^2175 ≤ (43645309697531/100000000000000 : ℝ)^1663
        have hw : |(1326285769/2500000000 : ℝ)|=(1326285769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082286163/2000000000 : ℝ)|^2175 ≤ (8958492833481/20000000000000 : ℝ)^1663
        have hw : |(1082286163/2000000000 : ℝ)|=(1082286163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1921337473/10000000000 : ℝ)|^2175 ≤ (2890556530227/25000000000000 : ℝ)^1663
        have hw : |(-1921337473/10000000000 : ℝ)|=(1921337473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s4_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4314124601/10000000000 : ℝ)*x 0 + (4495054491/10000000000 : ℝ)*x 1 + (827986773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314124601/10000000000 : ℝ)^2175 ≤ (6660616277397/20000000000000 : ℝ)^1663 := by
    have hnat : (4314124601 : ℕ)^2175*20000000000000^1663 ≤ 6660616277397^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314124601 10000000000 6660616277397 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495054491/10000000000 : ℝ)^2175 ≤ (35141470260357/100000000000000 : ℝ)^1663 := by
    have hnat : (4495054491 : ℕ)^2175*100000000000000^1663 ≤ 35141470260357^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495054491 10000000000 35141470260357 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827986773/2000000000 : ℝ)^2175 ≤ (6311089667471/20000000000000 : ℝ)^1663 := by
    have hnat : (827986773 : ℕ)^2175*20000000000000^1663 ≤ 6311089667471^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827986773 2000000000 6311089667471 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314124601/10000000000 : ℝ), (4495054491/10000000000 : ℝ), (827986773/2000000000 : ℝ)] ![(6660616277397/20000000000000 : ℝ), (35141470260357/100000000000000 : ℝ), (6311089667471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314124601/10000000000 : ℝ)|^2175 ≤ (6660616277397/20000000000000 : ℝ)^1663
        have hw : |(4314124601/10000000000 : ℝ)|=(4314124601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495054491/10000000000 : ℝ)|^2175 ≤ (35141470260357/100000000000000 : ℝ)^1663
        have hw : |(4495054491/10000000000 : ℝ)|=(4495054491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827986773/2000000000 : ℝ)|^2175 ≤ (6311089667471/20000000000000 : ℝ)^1663
        have hw : |(827986773/2000000000 : ℝ)|=(827986773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1497/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5611/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7387/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1497/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1497/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1497/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1497/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1497/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1497/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11037/100000 : ℝ) ^ (4349/1024 : ℝ) ≤ (2152093257471131/25000000000000000000 : ℝ) := by
    have hpowers : (11037/100000 : ℝ)^4349 ≤ (2152093257471131/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11037 : ℕ)^4349*25000000000000000000^1024 ≤ 2152093257471131^1024*100000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11037 100000 2152093257471131 25000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11037/100000 : ℝ)) (X := (2152093257471131/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1497/10000 : ℝ) ^ (4349/1024 : ℝ) ≤ (31412969586870321/100000000000000000000 : ℝ) := by
    have hpowers : (1497/10000 : ℝ)^4349 ≤ (31412969586870321/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1497 : ℕ)^4349*100000000000000000000^1024 ≤ 31412969586870321^1024*10000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1497 10000 31412969586870321 100000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1497/10000 : ℝ)) (X := (31412969586870321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502152093257471131/12500000000000000000 : ℝ) ≤ (10000405352673531/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (12502152093257471131/12500000000000000000 : ℝ)^1024 ≤ (10000405352673531/10000000000000000 : ℝ)^4349 := by
      have hnat : (12502152093257471131 : ℕ)^1024*10000000000000000^4349 ≤ 10000405352673531^4349*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502152093257471131 12500000000000000000 10000405352673531 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000405352673531/10000000000000000 : ℝ)) (X := (12502152093257471131/12500000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008004268523350969/20000000000000000000 : ℝ) ≤ (5000471092049767/5000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (20008004268523350969/20000000000000000000 : ℝ)^1024 ≤ (5000471092049767/5000000000000000 : ℝ)^4349 := by
      have hnat : (20008004268523350969 : ℕ)^1024*5000000000000000^4349 ≤ 5000471092049767^4349*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008004268523350969 20000000000000000000 5000471092049767 5000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000471092049767/5000000000000000 : ℝ)) (X := (20008004268523350969/20000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031412969586870321/50000000000000000000 : ℝ) ≤ (10001479015525537/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (50031412969586870321/50000000000000000000 : ℝ)^1024 ≤ (10001479015525537/10000000000000000 : ℝ)^4349 := by
      have hnat : (50031412969586870321 : ℕ)^1024*10000000000000000^4349 ≤ 10001479015525537^4349*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031412969586870321 50000000000000000000 10001479015525537 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001479015525537/10000000000000000 : ℝ)) (X := (50031412969586870321/50000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2152093257471131/25000000000000000000 : ℝ) ≤ ((13106581411722469067/13110000000000000000 : ℝ)+2*(536831426003/393300000000000 : ℝ)*(11037/100000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (13106581411722469067/13110000000000000000 : ℝ)+2*(536831426003/393300000000000 : ℝ)*(11037/100000 : ℝ)=(10000405352673531/10000000000000000 : ℝ) by norm_num, show 1+2*(2152093257471131/25000000000000000000 : ℝ)=(12502152093257471131/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31412969586870321/100000000000000000000 : ℝ)+(2152093257471131/25000000000000000000 : ℝ) ≤ ((13106581411722469067/13110000000000000000 : ℝ)+(536831426003/393300000000000 : ℝ)*((1497/10000 : ℝ)+(11037/100000 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (13106581411722469067/13110000000000000000 : ℝ)+(536831426003/393300000000000 : ℝ)*((1497/10000 : ℝ)+(11037/100000 : ℝ))=(5000471092049767/5000000000000000 : ℝ) by norm_num, show 1+(31412969586870321/100000000000000000000 : ℝ)+(2152093257471131/25000000000000000000 : ℝ)=(20008004268523350969/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31412969586870321/100000000000000000000 : ℝ) ≤ ((13106581411722469067/13110000000000000000 : ℝ)+2*(536831426003/393300000000000 : ℝ)*(1497/10000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (13106581411722469067/13110000000000000000 : ℝ)+2*(536831426003/393300000000000 : ℝ)*(1497/10000 : ℝ)=(10001479015525537/10000000000000000 : ℝ) by norm_num, show 1+2*(31412969586870321/100000000000000000000 : ℝ)=(50031412969586870321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13106581411722469067/13110000000000000000 : ℝ)*(X 1 0+X 2 0)+(536831426003/393300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (1497/10000 : ℝ)) (c := (13106581411722469067/13110000000000000000 : ℝ)) (alpha := (536831426003/393300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13106581411722469067/13110000000000000000 : ℝ)*(X 0 1+X 2 1)+(536831426003/393300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (1497/10000 : ℝ)) (c := (13106581411722469067/13110000000000000000 : ℝ)) (alpha := (536831426003/393300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13106581411722469067/13110000000000000000 : ℝ)*(X 0 2+X 1 2)+(536831426003/393300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (1497/10000 : ℝ)) (c := (13106581411722469067/13110000000000000000 : ℝ)) (alpha := (536831426003/393300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-125188141/625000000 : ℝ)*X 0 0+(5412049791/10000000000 : ℝ)*X 0 1+(1311071019/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348585119/10000000000 : ℝ)*X 1 0+(-1044242043/5000000000 : ℝ)*X 1 1+(5244284073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348585121/10000000000 : ℝ)*X 2 0+(1311071017/2500000000 : ℝ)*X 2 1+(-208848409/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431409803/1000000000 : ℝ)*X 0 0+(4138613779/10000000000 : ℝ)*X 0 1+(281022979/625000000 : ℝ)*X 0 2+(431409803/1000000000 : ℝ)*X 1 0+(4138613779/10000000000 : ℝ)*X 1 1+(281022979/625000000 : ℝ)*X 1 2+(431409803/1000000000 : ℝ)*X 2 0+(4138613779/10000000000 : ℝ)*X 2 1+(281022979/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2003022781/10000000000 : ℝ)*X 0 0+(524489981/1000000000 : ℝ)*X 0 1+(169107211/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326285783/2500000000 : ℝ)*X 1 0+(-960668681/5000000000 : ℝ)*X 1 1+(5411430841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326285769/2500000000 : ℝ)*X 2 0+(1082286163/2000000000 : ℝ)*X 2 1+(-1921337473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314124601/10000000000 : ℝ)*X 0 0+(4495054491/10000000000 : ℝ)*X 0 1+(827986773/2000000000 : ℝ)*X 0 2+(4314124601/10000000000 : ℝ)*X 1 0+(4495054491/10000000000 : ℝ)*X 1 1+(827986773/2000000000 : ℝ)*X 1 2+(4314124601/10000000000 : ℝ)*X 2 0+(4495054491/10000000000 : ℝ)*X 2 1+(827986773/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (337677635921101825380400683/109250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117104591/20000000000000 : ℝ)*(base19) + (550607953/100000000000000 : ℝ)*(base23) + (1986673/10000000000000 : ℝ)*(lower2) + (16018619/20000000000000 : ℝ)*(upper3) + (48259059/100000000000000 : ℝ)*(upper5) + (2188986701803083/50000000000000 : ℝ)*(major0) + (2188986701803083/50000000000000 : ℝ)*(major1) + (2188986701803083/50000000000000 : ℝ)*(major2) + (745088232879699/12500000000000 : ℝ)*(sp0) + (5960717038249517/100000000000000 : ℝ)*(sp1) + (5960717073164519/100000000000000 : ℝ)*(sp2) + (698805767538107/25000000000000 : ℝ)*(sp3) + (73504593/625000000000 : ℝ)*(sp4) + (6010258397/100000000000000 : ℝ)*(sp7) + (349403635051353/12500000000000 : ℝ)*(f.failure) + (745089702971559/12500000000000 : ℝ)*(f.sum) + (4315810810797/2185000000000000000000000000 : ℝ)*base65 + (1742461747636488813/218500000000000000000000000000000 : ℝ)*base68 + (1910856406589488813/218500000000000000000000000000000 : ℝ)*base70 + (1832188018592988813/218500000000000000000000000000000 : ℝ)*base72 + (8437014388523/2185000000000000000000000000 : ℝ)*base74 + (1328997022185988813/218500000000000000000000000000000 : ℝ)*base76 + (580922482898988813/218500000000000000000000000000000 : ℝ)*base78 + (2912194335206488813/218500000000000000000000000000000 : ℝ)*base80 + (8355011360373/2185000000000000000000000000 : ℝ)*base82 + (5845761/1250000000000000000000 : ℝ)*base90 + (5845761/1250000000000000000000 : ℝ)*base92 + (5845761/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40290608140543707409523/6555000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1085218723/100000000000000 : ℝ)*(base19) + (30627903/3125000000000 : ℝ)*(base23) + (66894777/50000000000000 : ℝ)*(upper3) + (1380073/100000000000000 : ℝ)*(lower4) + (16926271/10000000000000 : ℝ)*(upper5) + (4410417241378471/100000000000000 : ℝ)*(major0) + (4410417241378471/100000000000000 : ℝ)*(major1) + (4410417241378471/100000000000000 : ℝ)*(major2) + (24984873697/100000000000000 : ℝ)*(sp1) + (9784968453/50000000000000 : ℝ)*(sp2) + (6004890599527287/100000000000000 : ℝ)*(sp4) + (6004864529434867/100000000000000 : ℝ)*(sp5) + (1501217512374371/25000000000000 : ℝ)*(sp6) + (1407971839172393/50000000000000 : ℝ)*(sp7) + (1407971839172393/50000000000000 : ℝ)*(f.failure) + (6004890599527287/100000000000000 : ℝ)*(f.sum) + (75526157496761/9832500000000000000000000000 : ℝ)*base66 + (8476688300114930329/3933000000000000000000000000000000 : ℝ)*base68 + (19649145235191069671/3933000000000000000000000000000000 : ℝ)*base69 + (61666302539855930329/3933000000000000000000000000000000 : ℝ)*base72 + (132357857969963/19665000000000000000000000000 : ℝ)*base73 + (23018423609859069671/3933000000000000000000000000000000 : ℝ)*base75 + (8520845664314930329/3933000000000000000000000000000000 : ℝ)*base78 + (13518741636951069671/3933000000000000000000000000000000 : ℝ)*base79 + (88985232548557/19665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (26699759/5000000000000000000000 : ℝ)*base89 + (26699759/5000000000000000000000 : ℝ)*base91 + (26699759/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1390_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1497/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1390_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1390_s5_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001593821/5000000000 : ℝ)*x 0 + (5410484053/10000000000 : ℝ)*x 1 + (5245733039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001593821/5000000000 : ℝ)^2175 ≤ (6105307705167/50000000000000 : ℝ)^1663 := by
    have hnat : (1001593821 : ℕ)^2175*50000000000000^1663 ≤ 6105307705167^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001593821 5000000000 6105307705167 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410484053/10000000000 : ℝ)^2175 ≤ (11195553747693/25000000000000 : ℝ)^1663 := by
    have hnat : (5410484053 : ℕ)^2175*25000000000000^1663 ≤ 11195553747693^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410484053 10000000000 11195553747693 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245733039/10000000000 : ℝ)^2175 ≤ (43007169587263/100000000000000 : ℝ)^1663 := by
    have hnat : (5245733039 : ℕ)^2175*100000000000000^1663 ≤ 43007169587263^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245733039 10000000000 43007169587263 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001593821/5000000000 : ℝ), (5410484053/10000000000 : ℝ), (5245733039/10000000000 : ℝ)] ![(6105307705167/50000000000000 : ℝ), (11195553747693/25000000000000 : ℝ), (43007169587263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001593821/5000000000 : ℝ)|^2175 ≤ (6105307705167/50000000000000 : ℝ)^1663
        have hw : |(-1001593821/5000000000 : ℝ)|=(1001593821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410484053/10000000000 : ℝ)|^2175 ≤ (11195553747693/25000000000000 : ℝ)^1663
        have hw : |(5410484053/10000000000 : ℝ)|=(5410484053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245733039/10000000000 : ℝ)|^2175 ≤ (43007169587263/100000000000000 : ℝ)^1663
        have hw : |(5245733039/10000000000 : ℝ)|=(5245733039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s5_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (6685229/12500000 : ℝ)*x 0 + (-521774361/2500000000 : ℝ)*x 1 + (2622866321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6685229/12500000 : ℝ)^2175 ≤ (689203025377/1562500000000 : ℝ)^1663 := by
    have hnat : (6685229 : ℕ)^2175*1562500000000^1663 ≤ 689203025377^1663*12500000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6685229 12500000 689203025377 1562500000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521774361/2500000000 : ℝ)^2175 ≤ (12883841028399/100000000000000 : ℝ)^1663 := by
    have hnat : (521774361 : ℕ)^2175*100000000000000^1663 ≤ 12883841028399^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521774361 2500000000 12883841028399 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622866321/5000000000 : ℝ)^2175 ≤ (5375895666297/12500000000000 : ℝ)^1663 := by
    have hnat : (2622866321 : ℕ)^2175*12500000000000^1663 ≤ 5375895666297^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622866321 5000000000 5375895666297 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6685229/12500000 : ℝ), (-521774361/2500000000 : ℝ), (2622866321/5000000000 : ℝ)] ![(689203025377/1562500000000 : ℝ), (12883841028399/100000000000000 : ℝ), (5375895666297/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6685229/12500000 : ℝ)|^2175 ≤ (689203025377/1562500000000 : ℝ)^1663
        have hw : |(6685229/12500000 : ℝ)|=(6685229/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521774361/2500000000 : ℝ)|^2175 ≤ (12883841028399/100000000000000 : ℝ)^1663
        have hw : |(-521774361/2500000000 : ℝ)|=(521774361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622866321/5000000000 : ℝ)|^2175 ≤ (5375895666297/12500000000000 : ℝ)^1663
        have hw : |(2622866321/5000000000 : ℝ)|=(2622866321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s5_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668522799/1250000000 : ℝ)*x 0 + (655716629/1250000000 : ℝ)*x 1 + (-1043549003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668522799/1250000000 : ℝ)^2175 ≤ (44108984908489/100000000000000 : ℝ)^1663 := by
    have hnat : (668522799 : ℕ)^2175*100000000000000^1663 ≤ 44108984908489^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668522799 1250000000 44108984908489 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655716629/1250000000 : ℝ)^2175 ≤ (8601433902441/20000000000000 : ℝ)^1663 := by
    have hnat : (655716629 : ℕ)^2175*20000000000000^1663 ≤ 8601433902441^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655716629 1250000000 8601433902441 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043549003/5000000000 : ℝ)^2175 ≤ (3220961391447/25000000000000 : ℝ)^1663 := by
    have hnat : (1043549003 : ℕ)^2175*25000000000000^1663 ≤ 3220961391447^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043549003 5000000000 3220961391447 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668522799/1250000000 : ℝ), (655716629/1250000000 : ℝ), (-1043549003/5000000000 : ℝ)] ![(44108984908489/100000000000000 : ℝ), (8601433902441/20000000000000 : ℝ), (3220961391447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668522799/1250000000 : ℝ)|^2175 ≤ (44108984908489/100000000000000 : ℝ)^1663
        have hw : |(668522799/1250000000 : ℝ)|=(668522799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655716629/1250000000 : ℝ)|^2175 ≤ (8601433902441/20000000000000 : ℝ)^1663
        have hw : |(655716629/1250000000 : ℝ)|=(655716629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043549003/5000000000 : ℝ)|^2175 ≤ (3220961391447/25000000000000 : ℝ)^1663
        have hw : |(-1043549003/5000000000 : ℝ)|=(1043549003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s5_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4314205153/10000000000 : ℝ)*x 0 + (4141814361/10000000000 : ℝ)*x 1 + (4493141251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314205153/10000000000 : ℝ)^2175 ≤ (16651947329963/50000000000000 : ℝ)^1663 := by
    have hnat : (4314205153 : ℕ)^2175*50000000000000^1663 ≤ 16651947329963^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314205153 10000000000 16651947329963 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4141814361/10000000000 : ℝ)^2175 ≤ (15787098077941/50000000000000 : ℝ)^1663 := by
    have hnat : (4141814361 : ℕ)^2175*50000000000000^1663 ≤ 15787098077941^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141814361 10000000000 15787098077941 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493141251/10000000000 : ℝ)^2175 ≤ (35121909173937/100000000000000 : ℝ)^1663 := by
    have hnat : (4493141251 : ℕ)^2175*100000000000000^1663 ≤ 35121909173937^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493141251 10000000000 35121909173937 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314205153/10000000000 : ℝ), (4141814361/10000000000 : ℝ), (4493141251/10000000000 : ℝ)] ![(16651947329963/50000000000000 : ℝ), (15787098077941/50000000000000 : ℝ), (35121909173937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314205153/10000000000 : ℝ)|^2175 ≤ (16651947329963/50000000000000 : ℝ)^1663
        have hw : |(4314205153/10000000000 : ℝ)|=(4314205153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4141814361/10000000000 : ℝ)|^2175 ≤ (15787098077941/50000000000000 : ℝ)^1663
        have hw : |(4141814361/10000000000 : ℝ)|=(4141814361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493141251/10000000000 : ℝ)|^2175 ≤ (35121909173937/100000000000000 : ℝ)^1663
        have hw : |(4493141251/10000000000 : ℝ)|=(4493141251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s5_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003199629/10000000000 : ℝ)*x 0 + (655790817/1250000000 : ℝ)*x 1 + (5409887331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003199629/10000000000 : ℝ)^2175 ≤ (3052677743557/25000000000000 : ℝ)^1663 := by
    have hnat : (2003199629 : ℕ)^2175*25000000000000^1663 ≤ 3052677743557^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003199629 10000000000 3052677743557 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655790817/1250000000 : ℝ)^2175 ≤ (10753383388057/25000000000000 : ℝ)^1663 := by
    have hnat : (655790817 : ℕ)^2175*25000000000000^1663 ≤ 10753383388057^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655790817 1250000000 10753383388057 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409887331/10000000000 : ℝ)^2175 ≤ (11193938864383/25000000000000 : ℝ)^1663 := by
    have hnat : (5409887331 : ℕ)^2175*25000000000000^1663 ≤ 11193938864383^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409887331 10000000000 11193938864383 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003199629/10000000000 : ℝ), (655790817/1250000000 : ℝ), (5409887331/10000000000 : ℝ)] ![(3052677743557/25000000000000 : ℝ), (10753383388057/25000000000000 : ℝ), (11193938864383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003199629/10000000000 : ℝ)|^2175 ≤ (3052677743557/25000000000000 : ℝ)^1663
        have hw : |(-2003199629/10000000000 : ℝ)|=(2003199629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655790817/1250000000 : ℝ)|^2175 ≤ (10753383388057/25000000000000 : ℝ)^1663
        have hw : |(655790817/1250000000 : ℝ)|=(655790817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409887331/10000000000 : ℝ)|^2175 ≤ (11193938864383/25000000000000 : ℝ)^1663
        have hw : |(5409887331/10000000000 : ℝ)|=(5409887331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s5_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331595083/625000000 : ℝ)*x 0 + (-1922943307/10000000000 : ℝ)*x 1 + (2704943587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331595083/625000000 : ℝ)^2175 ≤ (21824689844459/50000000000000 : ℝ)^1663 := by
    have hnat : (331595083 : ℕ)^2175*50000000000000^1663 ≤ 21824689844459^1663*625000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331595083 625000000 21824689844459 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1922943307/10000000000 : ℝ)^2175 ≤ (1157486653579/10000000000000 : ℝ)^1663 := by
    have hnat : (1922943307 : ℕ)^2175*10000000000000^1663 ≤ 1157486653579^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922943307 10000000000 1157486653579 10000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704943587/5000000000 : ℝ)^2175 ≤ (44775753758031/100000000000000 : ℝ)^1663 := by
    have hnat : (2704943587 : ℕ)^2175*100000000000000^1663 ≤ 44775753758031^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704943587 5000000000 44775753758031 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331595083/625000000 : ℝ), (-1922943307/10000000000 : ℝ), (2704943587/5000000000 : ℝ)] ![(21824689844459/50000000000000 : ℝ), (1157486653579/10000000000000 : ℝ), (44775753758031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331595083/625000000 : ℝ)|^2175 ≤ (21824689844459/50000000000000 : ℝ)^1663
        have hw : |(331595083/625000000 : ℝ)|=(331595083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1922943307/10000000000 : ℝ)|^2175 ≤ (1157486653579/10000000000000 : ℝ)^1663
        have hw : |(-1922943307/10000000000 : ℝ)|=(1922943307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704943587/5000000000 : ℝ)|^2175 ≤ (44775753758031/100000000000000 : ℝ)^1663
        have hw : |(2704943587/5000000000 : ℝ)|=(2704943587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s5_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305521401/10000000000 : ℝ)*x 0 + (5409886981/10000000000 : ℝ)*x 1 + (-1922943473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305521401/10000000000 : ℝ)^2175 ≤ (21824690237203/50000000000000 : ℝ)^1663 := by
    have hnat : (5305521401 : ℕ)^2175*50000000000000^1663 ≤ 21824690237203^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305521401 10000000000 21824690237203 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409886981/10000000000 : ℝ)^2175 ≤ (11193937917209/25000000000000 : ℝ)^1663 := by
    have hnat : (5409886981 : ℕ)^2175*25000000000000^1663 ≤ 11193937917209^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409886981 10000000000 11193937917209 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1922943473/10000000000 : ℝ)^2175 ≤ (2893716960659/25000000000000 : ℝ)^1663 := by
    have hnat : (1922943473 : ℕ)^2175*25000000000000^1663 ≤ 2893716960659^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922943473 10000000000 2893716960659 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305521401/10000000000 : ℝ), (5409886981/10000000000 : ℝ), (-1922943473/10000000000 : ℝ)] ![(21824690237203/50000000000000 : ℝ), (11193937917209/25000000000000 : ℝ), (2893716960659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305521401/10000000000 : ℝ)|^2175 ≤ (21824690237203/50000000000000 : ℝ)^1663
        have hw : |(5305521401/10000000000 : ℝ)|=(5305521401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409886981/10000000000 : ℝ)|^2175 ≤ (11193937917209/25000000000000 : ℝ)^1663
        have hw : |(5409886981/10000000000 : ℝ)|=(5409886981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1922943473/10000000000 : ℝ)|^2175 ≤ (2893716960659/25000000000000 : ℝ)^1663
        have hw : |(-1922943473/10000000000 : ℝ)|=(1922943473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s5_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4314230823/10000000000 : ℝ)*x 0 + (4491874011/10000000000 : ℝ)*x 1 + (4143087657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314230823/10000000000 : ℝ)^2175 ≤ (16652076915793/50000000000000 : ℝ)^1663 := by
    have hnat : (4314230823 : ℕ)^2175*50000000000000^1663 ≤ 16652076915793^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314230823 10000000000 16652076915793 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491874011/10000000000 : ℝ)^2175 ≤ (35108954243917/100000000000000 : ℝ)^1663 := by
    have hnat : (4491874011 : ℕ)^2175*100000000000000^1663 ≤ 35108954243917^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491874011 10000000000 35108954243917 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143087657/10000000000 : ℝ)^2175 ≤ (31586891913159/100000000000000 : ℝ)^1663 := by
    have hnat : (4143087657 : ℕ)^2175*100000000000000^1663 ≤ 31586891913159^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143087657 10000000000 31586891913159 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314230823/10000000000 : ℝ), (4491874011/10000000000 : ℝ), (4143087657/10000000000 : ℝ)] ![(16652076915793/50000000000000 : ℝ), (35108954243917/100000000000000 : ℝ), (31586891913159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314230823/10000000000 : ℝ)|^2175 ≤ (16652076915793/50000000000000 : ℝ)^1663
        have hw : |(4314230823/10000000000 : ℝ)|=(4314230823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491874011/10000000000 : ℝ)|^2175 ≤ (35108954243917/100000000000000 : ℝ)^1663
        have hw : |(4491874011/10000000000 : ℝ)|=(4491874011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143087657/10000000000 : ℝ)|^2175 ≤ (31586891913159/100000000000000 : ℝ)^1663
        have hw : |(4143087657/10000000000 : ℝ)|=(4143087657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14741/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5611/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5611/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5611/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5611/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5611/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5611/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5611/50000 : ℝ) ^ (4349/1024 : ℝ) ≤ (923807791540281/10000000000000000000 : ℝ) := by
    have hpowers : (5611/50000 : ℝ)^4349 ≤ (923807791540281/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5611 : ℕ)^4349*10000000000000000000^1024 ≤ 923807791540281^1024*50000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5611 50000 923807791540281 10000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5611/50000 : ℝ)) (X := (923807791540281/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7387/50000 : ℝ) ^ (4349/1024 : ℝ) ≤ (14851489680441453/50000000000000000000 : ℝ) := by
    have hpowers : (7387/50000 : ℝ)^4349 ≤ (14851489680441453/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7387 : ℕ)^4349*50000000000000000000^1024 ≤ 14851489680441453^1024*50000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7387 50000 14851489680441453 50000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7387/50000 : ℝ)) (X := (14851489680441453/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000923807791540281/5000000000000000000 : ℝ) ≤ (5000217501120283/5000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (5000923807791540281/5000000000000000000 : ℝ)^1024 ≤ (5000217501120283/5000000000000000 : ℝ)^4349 := by
      have hnat : (5000923807791540281 : ℕ)^1024*5000000000000000^4349 ≤ 5000217501120283^4349*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000923807791540281 5000000000000000000 5000217501120283 5000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000217501120283/5000000000000000 : ℝ)) (X := (5000923807791540281/5000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009735264319071429/25000000000000000000 : ℝ) ≤ (10000916755762131/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (25009735264319071429/25000000000000000000 : ℝ)^1024 ≤ (10000916755762131/10000000000000000 : ℝ)^4349 := by
      have hnat : (25009735264319071429 : ℕ)^1024*10000000000000000^4349 ≤ 10000916755762131^4349*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009735264319071429 25000000000000000000 10000916755762131 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000916755762131/10000000000000000 : ℝ)) (X := (25009735264319071429/25000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014851489680441453/25000000000000000000 : ℝ) ≤ (625087406830231/625000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (25014851489680441453/25000000000000000000 : ℝ)^1024 ≤ (625087406830231/625000000000000 : ℝ)^4349 := by
      have hnat : (25014851489680441453 : ℕ)^1024*625000000000000^4349 ≤ 625087406830231^4349*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014851489680441453 25000000000000000000 625087406830231 625000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625087406830231/625000000000000 : ℝ)) (X := (25014851489680441453/25000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(923807791540281/10000000000000000000 : ℝ) ≤ ((8877683162980121393/8880000000000000000 : ℝ)+2*(96350704313/71040000000000 : ℝ)*(5611/50000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (8877683162980121393/8880000000000000000 : ℝ)+2*(96350704313/71040000000000 : ℝ)*(5611/50000 : ℝ)=(5000217501120283/5000000000000000 : ℝ) by norm_num, show 1+2*(923807791540281/10000000000000000000 : ℝ)=(5000923807791540281/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14851489680441453/50000000000000000000 : ℝ)+(923807791540281/10000000000000000000 : ℝ) ≤ ((8877683162980121393/8880000000000000000 : ℝ)+(96350704313/71040000000000 : ℝ)*((7387/50000 : ℝ)+(5611/50000 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (8877683162980121393/8880000000000000000 : ℝ)+(96350704313/71040000000000 : ℝ)*((7387/50000 : ℝ)+(5611/50000 : ℝ))=(10000916755762131/10000000000000000 : ℝ) by norm_num, show 1+(14851489680441453/50000000000000000000 : ℝ)+(923807791540281/10000000000000000000 : ℝ)=(25009735264319071429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14851489680441453/50000000000000000000 : ℝ) ≤ ((8877683162980121393/8880000000000000000 : ℝ)+2*(96350704313/71040000000000 : ℝ)*(7387/50000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (8877683162980121393/8880000000000000000 : ℝ)+2*(96350704313/71040000000000 : ℝ)*(7387/50000 : ℝ)=(625087406830231/625000000000000 : ℝ) by norm_num, show 1+2*(14851489680441453/50000000000000000000 : ℝ)=(25014851489680441453/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8877683162980121393/8880000000000000000 : ℝ)*(X 1 0+X 2 0)+(96350704313/71040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (8877683162980121393/8880000000000000000 : ℝ)) (alpha := (96350704313/71040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8877683162980121393/8880000000000000000 : ℝ)*(X 0 1+X 2 1)+(96350704313/71040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (8877683162980121393/8880000000000000000 : ℝ)) (alpha := (96350704313/71040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8877683162980121393/8880000000000000000 : ℝ)*(X 0 2+X 1 2)+(96350704313/71040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (8877683162980121393/8880000000000000000 : ℝ)) (alpha := (96350704313/71040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1001593821/5000000000 : ℝ)*X 0 0+(5410484053/10000000000 : ℝ)*X 0 1+(5245733039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((6685229/12500000 : ℝ)*X 1 0+(-521774361/2500000000 : ℝ)*X 1 1+(2622866321/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668522799/1250000000 : ℝ)*X 2 0+(655716629/1250000000 : ℝ)*X 2 1+(-1043549003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314205153/10000000000 : ℝ)*X 0 0+(4141814361/10000000000 : ℝ)*X 0 1+(4493141251/10000000000 : ℝ)*X 0 2+(4314205153/10000000000 : ℝ)*X 1 0+(4141814361/10000000000 : ℝ)*X 1 1+(4493141251/10000000000 : ℝ)*X 1 2+(4314205153/10000000000 : ℝ)*X 2 0+(4141814361/10000000000 : ℝ)*X 2 1+(4493141251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2003199629/10000000000 : ℝ)*X 0 0+(655790817/1250000000 : ℝ)*X 0 1+(5409887331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331595083/625000000 : ℝ)*X 1 0+(-1922943307/10000000000 : ℝ)*X 1 1+(2704943587/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305521401/10000000000 : ℝ)*X 2 0+(5409886981/10000000000 : ℝ)*X 2 1+(-1922943473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314230823/10000000000 : ℝ)*X 0 0+(4491874011/10000000000 : ℝ)*X 0 1+(4143087657/10000000000 : ℝ)*X 0 2+(4314230823/10000000000 : ℝ)*X 1 0+(4491874011/10000000000 : ℝ)*X 1 1+(4143087657/10000000000 : ℝ)*X 1 2+(4314230823/10000000000 : ℝ)*X 2 0+(4491874011/10000000000 : ℝ)*X 2 1+(4143087657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5380721796037844779561143/2000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109340777/20000000000000 : ℝ)*(base19) + (129612667/100000000000000 : ℝ)*(upper2) + (122449271/100000000000000 : ℝ)*(lower4) + (5387533/5000000000000 : ℝ)*(lower5) + (4458080510770287/100000000000000 : ℝ)*(major0) + (4458080510770287/100000000000000 : ℝ)*(major1) + (4458080510770287/100000000000000 : ℝ)*(major2) + (94840379156563/1562500000000 : ℝ)*(sp0) + (6069784873544929/100000000000000 : ℝ)*(sp1) + (6069772759846947/100000000000000 : ℝ)*(sp2) + (1423182856747341/50000000000000 : ℝ)*(sp3) + (1154228781/100000000000000 : ℝ)*(sp4) + (12660401867/100000000000000 : ℝ)*(sp6) + (9798118373/100000000000000 : ℝ)*(sp7) + (569275102322611/20000000000000 : ℝ)*(f.failure) + (3034892710124407/50000000000000 : ℝ)*(f.sum) + (534503106503/32000000000000000000000000 : ℝ)*base66 + (100432160065042119/8000000000000000000000000000000 : ℝ)*base68 + (42852276854957881/8000000000000000000000000000000 : ℝ)*base69 + (34797644129042119/8000000000000000000000000000000 : ℝ)*base72 + (78763123993/32000000000000000000000000 : ℝ)*base73 + (117173016417042119/8000000000000000000000000000000 : ℝ)*base76 + (62527404857042119/8000000000000000000000000000000 : ℝ)*base78 + (39343076217042119/8000000000000000000000000000000 : ℝ)*base80 + (22389728519/32000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (8977493/2000000000000000000000 : ℝ)*base89 + (8977493/2000000000000000000000 : ℝ)*base91 + (8977493/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171428769847497111370805833/74000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (939337787/100000000000000 : ℝ)*(base19) + (197605783/20000000000000 : ℝ)*(base23) + (21154001/100000000000000 : ℝ)*(lower4) + (137633277/100000000000000 : ℝ)*(upper5) + (2245256187811081/50000000000000 : ℝ)*(major0) + (2245256187811081/50000000000000 : ℝ)*(major1) + (2245256187811081/50000000000000 : ℝ)*(major2) + (172361953/12500000000000 : ℝ)*(sp0) + (5449330413/25000000000000 : ℝ)*(sp1) + (6216318879/50000000000000 : ℝ)*(sp2) + (3056970414999377/50000000000000 : ℝ)*(sp4) + (6113919472234939/100000000000000 : ℝ)*(sp5) + (1222785757645541/20000000000000 : ℝ)*(sp6) + (179192654070611/6250000000000 : ℝ)*(sp7) + (179192654070611/6250000000000 : ℝ)*(f.failure) + (3056971104447189/50000000000000 : ℝ)*(f.sum) + (7835747573729/1776000000000000000000000000 : ℝ)*base65 + (618531427671106389/148000000000000000000000000000000 : ℝ)*base68 + (1147425706191106389/148000000000000000000000000000000 : ℝ)*base70 + (519449557704893611/148000000000000000000000000000000 : ℝ)*base71 + (5863687724047/1776000000000000000000000000 : ℝ)*base74 + (780508555071106389/148000000000000000000000000000000 : ℝ)*base76 + (182801883252893611/148000000000000000000000000000000 : ℝ)*base77 + (176516203131106389/148000000000000000000000000000000 : ℝ)*base80 + (3908585306191/1776000000000000000000000000 : ℝ)*base82 + (601493/625000000000000000000 : ℝ)*base89 + (601493/625000000000000000000 : ℝ)*base91 + (601493/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1390_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1390_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1390_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7963/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1390_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1390_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1390_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7963/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1390_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
