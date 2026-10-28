-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1277_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:46.097968+00:00
-- url     : https://prove2.me/submissions/93aa053f-7e1f-4472-a8ef-d0cb0e42e866

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
theorem support_rectangle_w1277_s0_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1848204591/10000000000 : ℝ)*x 0 + (6025466527/10000000000 : ℝ)*x 1 + (2397582821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1848204591/10000000000 : ℝ)^4237 ≤ (2158188742333/20000000000000 : ℝ)^3213 := by
    have hnat : (1848204591 : ℕ)^4237*20000000000000^3213 ≤ 2158188742333^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848204591 10000000000 2158188742333 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6025466527/10000000000 : ℝ)^4237 ≤ (25635544979261/50000000000000 : ℝ)^3213 := by
    have hnat : (6025466527 : ℕ)^4237*50000000000000^3213 ≤ 25635544979261^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6025466527 10000000000 25635544979261 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397582821/5000000000 : ℝ)^4237 ≤ (7587593263709/20000000000000 : ℝ)^3213 := by
    have hnat : (2397582821 : ℕ)^4237*20000000000000^3213 ≤ 7587593263709^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397582821 5000000000 7587593263709 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1848204591/10000000000 : ℝ), (6025466527/10000000000 : ℝ), (2397582821/5000000000 : ℝ)] ![(2158188742333/20000000000000 : ℝ), (25635544979261/50000000000000 : ℝ), (7587593263709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1848204591/10000000000 : ℝ)|^4237 ≤ (2158188742333/20000000000000 : ℝ)^3213
        have hw : |(-1848204591/10000000000 : ℝ)|=(1848204591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6025466527/10000000000 : ℝ)|^4237 ≤ (25635544979261/50000000000000 : ℝ)^3213
        have hw : |(6025466527/10000000000 : ℝ)|=(6025466527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397582821/5000000000 : ℝ)|^4237 ≤ (7587593263709/20000000000000 : ℝ)^3213
        have hw : |(2397582821/5000000000 : ℝ)|=(2397582821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s0_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (110182047/200000000 : ℝ)*x 0 + (-318859199/1250000000 : ℝ)*x 1 + (959033123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110182047/200000000 : ℝ)^4237 ≤ (22778858004977/50000000000000 : ℝ)^3213 := by
    have hnat : (110182047 : ℕ)^4237*50000000000000^3213 ≤ 22778858004977^3213*200000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110182047 200000000 22778858004977 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318859199/1250000000 : ℝ)^4237 ≤ (16504317946759/100000000000000 : ℝ)^3213 := by
    have hnat : (318859199 : ℕ)^4237*100000000000000^3213 ≤ 16504317946759^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318859199 1250000000 16504317946759 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959033123/2000000000 : ℝ)^4237 ≤ (2371122877303/6250000000000 : ℝ)^3213 := by
    have hnat : (959033123 : ℕ)^4237*6250000000000^3213 ≤ 2371122877303^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959033123 2000000000 2371122877303 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110182047/200000000 : ℝ), (-318859199/1250000000 : ℝ), (959033123/2000000000 : ℝ)] ![(22778858004977/50000000000000 : ℝ), (16504317946759/100000000000000 : ℝ), (2371122877303/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110182047/200000000 : ℝ)|^4237 ≤ (22778858004977/50000000000000 : ℝ)^3213
        have hw : |(110182047/200000000 : ℝ)|=(110182047/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-318859199/1250000000 : ℝ)|^4237 ≤ (16504317946759/100000000000000 : ℝ)^3213
        have hw : |(-318859199/1250000000 : ℝ)|=(318859199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(959033123/2000000000 : ℝ)|^4237 ≤ (2371122877303/6250000000000 : ℝ)^3213
        have hw : |(959033123/2000000000 : ℝ)|=(959033123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s0_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1377275591/2500000000 : ℝ)*x 0 + (4795165619/10000000000 : ℝ)*x 1 + (-79714799/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377275591/2500000000 : ℝ)^4237 ≤ (22778858081313/50000000000000 : ℝ)^3213 := by
    have hnat : (1377275591 : ℕ)^4237*50000000000000^3213 ≤ 22778858081313^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377275591 2500000000 22778858081313 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4795165619/10000000000 : ℝ)^4237 ≤ (37937966078581/100000000000000 : ℝ)^3213 := by
    have hnat : (4795165619 : ℕ)^4237*100000000000000^3213 ≤ 37937966078581^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795165619 10000000000 37937966078581 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79714799/312500000 : ℝ)^4237 ≤ (4126079435497/25000000000000 : ℝ)^3213 := by
    have hnat : (79714799 : ℕ)^4237*25000000000000^3213 ≤ 4126079435497^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79714799 312500000 4126079435497 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377275591/2500000000 : ℝ), (4795165619/10000000000 : ℝ), (-79714799/312500000 : ℝ)] ![(22778858081313/50000000000000 : ℝ), (37937966078581/100000000000000 : ℝ), (4126079435497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377275591/2500000000 : ℝ)|^4237 ≤ (22778858081313/50000000000000 : ℝ)^3213
        have hw : |(1377275591/2500000000 : ℝ)|=(1377275591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4795165619/10000000000 : ℝ)|^4237 ≤ (37937966078581/100000000000000 : ℝ)^3213
        have hw : |(4795165619/10000000000 : ℝ)|=(4795165619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79714799/312500000 : ℝ)|^4237 ≤ (4126079435497/25000000000000 : ℝ)^3213
        have hw : |(-79714799/312500000 : ℝ)|=(79714799/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s0_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2094323569/5000000000 : ℝ)*x 0 + (3110450437/10000000000 : ℝ)*x 1 + (5624525513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094323569/5000000000 : ℝ)^4237 ≤ (15870722743209/50000000000000 : ℝ)^3213 := by
    have hnat : (2094323569 : ℕ)^4237*50000000000000^3213 ≤ 15870722743209^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094323569 5000000000 15870722743209 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3110450437/10000000000 : ℝ)^4237 ≤ (167484040397/781250000000 : ℝ)^3213 := by
    have hnat : (3110450437 : ℕ)^4237*781250000000^3213 ≤ 167484040397^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110450437 10000000000 167484040397 781250000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5624525513/10000000000 : ℝ)^4237 ≤ (46820597330311/100000000000000 : ℝ)^3213 := by
    have hnat : (5624525513 : ℕ)^4237*100000000000000^3213 ≤ 46820597330311^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5624525513 10000000000 46820597330311 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094323569/5000000000 : ℝ), (3110450437/10000000000 : ℝ), (5624525513/10000000000 : ℝ)] ![(15870722743209/50000000000000 : ℝ), (167484040397/781250000000 : ℝ), (46820597330311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094323569/5000000000 : ℝ)|^4237 ≤ (15870722743209/50000000000000 : ℝ)^3213
        have hw : |(2094323569/5000000000 : ℝ)|=(2094323569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3110450437/10000000000 : ℝ)|^4237 ≤ (167484040397/781250000000 : ℝ)^3213
        have hw : |(3110450437/10000000000 : ℝ)|=(3110450437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5624525513/10000000000 : ℝ)|^4237 ≤ (46820597330311/100000000000000 : ℝ)^3213
        have hw : |(5624525513/10000000000 : ℝ)|=(5624525513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s0_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7412047/40000000 : ℝ)*x 0 + (4826940793/10000000000 : ℝ)*x 1 + (749070297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7412047/40000000 : ℝ)^4237 ≤ (10827971303549/100000000000000 : ℝ)^3213 := by
    have hnat : (7412047 : ℕ)^4237*100000000000000^3213 ≤ 10827971303549^3213*40000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7412047 40000000 10827971303549 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4826940793/10000000000 : ℝ)^4237 ≤ (38269832851327/100000000000000 : ℝ)^3213 := by
    have hnat : (4826940793 : ℕ)^4237*100000000000000^3213 ≤ 38269832851327^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826940793 10000000000 38269832851327 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (749070297/1250000000 : ℝ)^4237 ≤ (50902195830751/100000000000000 : ℝ)^3213 := by
    have hnat : (749070297 : ℕ)^4237*100000000000000^3213 ≤ 50902195830751^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749070297 1250000000 50902195830751 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7412047/40000000 : ℝ), (4826940793/10000000000 : ℝ), (749070297/1250000000 : ℝ)] ![(10827971303549/100000000000000 : ℝ), (38269832851327/100000000000000 : ℝ), (50902195830751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7412047/40000000 : ℝ)|^4237 ≤ (10827971303549/100000000000000 : ℝ)^3213
        have hw : |(-7412047/40000000 : ℝ)|=(7412047/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4826940793/10000000000 : ℝ)|^4237 ≤ (38269832851327/100000000000000 : ℝ)^3213
        have hw : |(4826940793/10000000000 : ℝ)|=(4826940793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(749070297/1250000000 : ℝ)|^4237 ≤ (50902195830751/100000000000000 : ℝ)^3213
        have hw : |(749070297/1250000000 : ℝ)|=(749070297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s0_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (323392409/625000000 : ℝ)*x 0 + (-169184307/1250000000 : ℝ)*x 1 + (5992564833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323392409/625000000 : ℝ)^4237 ≤ (41942298967359/100000000000000 : ℝ)^3213 := by
    have hnat : (323392409 : ℕ)^4237*100000000000000^3213 ≤ 41942298967359^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323392409 625000000 41942298967359 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169184307/1250000000 : ℝ)^4237 ≤ (7155477668031/100000000000000 : ℝ)^3213 := by
    have hnat : (169184307 : ℕ)^4237*100000000000000^3213 ≤ 7155477668031^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169184307 1250000000 7155477668031 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5992564833/10000000000 : ℝ)^4237 ≤ (25451111676277/50000000000000 : ℝ)^3213 := by
    have hnat : (5992564833 : ℕ)^4237*50000000000000^3213 ≤ 25451111676277^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5992564833 10000000000 25451111676277 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323392409/625000000 : ℝ), (-169184307/1250000000 : ℝ), (5992564833/10000000000 : ℝ)] ![(41942298967359/100000000000000 : ℝ), (7155477668031/100000000000000 : ℝ), (25451111676277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323392409/625000000 : ℝ)|^4237 ≤ (41942298967359/100000000000000 : ℝ)^3213
        have hw : |(323392409/625000000 : ℝ)|=(323392409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169184307/1250000000 : ℝ)|^4237 ≤ (7155477668031/100000000000000 : ℝ)^3213
        have hw : |(-169184307/1250000000 : ℝ)|=(169184307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5992564833/10000000000 : ℝ)|^4237 ≤ (25451111676277/50000000000000 : ℝ)^3213
        have hw : |(5992564833/10000000000 : ℝ)|=(5992564833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s0_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (517427971/1000000000 : ℝ)*x 0 + (1198512559/2000000000 : ℝ)*x 1 + (-676737971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517427971/1000000000 : ℝ)^4237 ≤ (4194231143111/10000000000000 : ℝ)^3213 := by
    have hnat : (517427971 : ℕ)^4237*10000000000000^3213 ≤ 4194231143111^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517427971 1000000000 4194231143111 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198512559/2000000000 : ℝ)^4237 ≤ (50902200524131/100000000000000 : ℝ)^3213 := by
    have hnat : (1198512559 : ℕ)^4237*100000000000000^3213 ≤ 50902200524131^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198512559 2000000000 50902200524131 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676737971/5000000000 : ℝ)^4237 ≤ (3577744013961/50000000000000 : ℝ)^3213 := by
    have hnat : (676737971 : ℕ)^4237*50000000000000^3213 ≤ 3577744013961^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676737971 5000000000 3577744013961 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517427971/1000000000 : ℝ), (1198512559/2000000000 : ℝ), (-676737971/5000000000 : ℝ)] ![(4194231143111/10000000000000 : ℝ), (50902200524131/100000000000000 : ℝ), (3577744013961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517427971/1000000000 : ℝ)|^4237 ≤ (4194231143111/10000000000000 : ℝ)^3213
        have hw : |(517427971/1000000000 : ℝ)|=(517427971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1198512559/2000000000 : ℝ)|^4237 ≤ (50902200524131/100000000000000 : ℝ)^3213
        have hw : |(1198512559/2000000000 : ℝ)|=(1198512559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-676737971/5000000000 : ℝ)|^4237 ≤ (3577744013961/50000000000000 : ℝ)^3213
        have hw : |(-676737971/5000000000 : ℝ)|=(676737971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s0_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524809241/1250000000 : ℝ)*x 0 + (277980021/500000000 : ℝ)*x 1 + (3177682627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524809241/1250000000 : ℝ)^4237 ≤ (6367936474257/20000000000000 : ℝ)^3213 := by
    have hnat : (524809241 : ℕ)^4237*20000000000000^3213 ≤ 6367936474257^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524809241 1250000000 6367936474257 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277980021/500000000 : ℝ)^4237 ≤ (230546020937/500000000000 : ℝ)^3213 := by
    have hnat : (277980021 : ℕ)^4237*500000000000^3213 ≤ 230546020937^3213*500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277980021 500000000 230546020937 500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3177682627/10000000000 : ℝ)^4237 ≤ (441022268721/2000000000000 : ℝ)^3213 := by
    have hnat : (3177682627 : ℕ)^4237*2000000000000^3213 ≤ 441022268721^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177682627 10000000000 441022268721 2000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524809241/1250000000 : ℝ), (277980021/500000000 : ℝ), (3177682627/10000000000 : ℝ)] ![(6367936474257/20000000000000 : ℝ), (230546020937/500000000000 : ℝ), (441022268721/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524809241/1250000000 : ℝ)|^4237 ≤ (6367936474257/20000000000000 : ℝ)^3213
        have hw : |(524809241/1250000000 : ℝ)|=(524809241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(277980021/500000000 : ℝ)|^4237 ≤ (230546020937/500000000000 : ℝ)^3213
        have hw : |(277980021/500000000 : ℝ)|=(277980021/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3177682627/10000000000 : ℝ)|^4237 ≤ (441022268721/2000000000000 : ℝ)^3213
        have hw : |(3177682627/10000000000 : ℝ)|=(3177682627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (183/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13673/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1059/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1059 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1059*1^256 ≤ 0^256*1^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1059/256 : ℝ) ≤ (2258572857856826391/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1059 ≤ (2258572857856826391/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1059*100000000000000000000^256 ≤ 2258572857856826391^256*5^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2258572857856826391 100000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2258572857856826391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1059 := by
      have hnat : (1 : ℕ)^256*1^1059 ≤ 1^1059*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102258572857856826391/100000000000000000000 : ℝ) ≤ (10054136745131273/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (102258572857856826391/100000000000000000000 : ℝ)^256 ≤ (10054136745131273/10000000000000000 : ℝ)^1059 := by
      have hnat : (102258572857856826391 : ℕ)^256*10000000000000000^1059 ≤ 10054136745131273^1059*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102258572857856826391 100000000000000000000 10054136745131273 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054136745131273/10000000000000000 : ℝ)) (X := (102258572857856826391/100000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52258572857856826391/50000000000000000000 : ℝ) ≤ (5054136745131273/5000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (52258572857856826391/50000000000000000000 : ℝ)^256 ≤ (5054136745131273/5000000000000000 : ℝ)^1059 := by
      have hnat : (52258572857856826391 : ℕ)^256*5000000000000000^1059 ≤ 5054136745131273^1059*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52258572857856826391 50000000000000000000 5054136745131273 5000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054136745131273/5000000000000000 : ℝ)) (X := (52258572857856826391/50000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54136745131273/4000000000000000 : ℝ)*(0 : ℝ))^(1059/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(54136745131273/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2258572857856826391/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54136745131273/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (1 : ℝ)+(54136745131273/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054136745131273/10000000000000000 : ℝ) by norm_num, show 1+(2258572857856826391/100000000000000000000 : ℝ)+(0 : ℝ)=(102258572857856826391/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2258572857856826391/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54136745131273/4000000000000000 : ℝ)*(2/5 : ℝ))^(1059/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(54136745131273/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054136745131273/5000000000000000 : ℝ) by norm_num, show 1+2*(2258572857856826391/100000000000000000000 : ℝ)=(52258572857856826391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54136745131273/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54136745131273/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54136745131273/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54136745131273/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54136745131273/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54136745131273/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1848204591/10000000000 : ℝ)*X 0 0+(6025466527/10000000000 : ℝ)*X 0 1+(2397582821/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((110182047/200000000 : ℝ)*X 1 0+(-318859199/1250000000 : ℝ)*X 1 1+(959033123/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1377275591/2500000000 : ℝ)*X 2 0+(4795165619/10000000000 : ℝ)*X 2 1+(-79714799/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2094323569/5000000000 : ℝ)*X 0 0+(3110450437/10000000000 : ℝ)*X 0 1+(5624525513/10000000000 : ℝ)*X 0 2+(2094323569/5000000000 : ℝ)*X 1 0+(3110450437/10000000000 : ℝ)*X 1 1+(5624525513/10000000000 : ℝ)*X 1 2+(2094323569/5000000000 : ℝ)*X 2 0+(3110450437/10000000000 : ℝ)*X 2 1+(5624525513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7412047/40000000 : ℝ)*X 0 0+(4826940793/10000000000 : ℝ)*X 0 1+(749070297/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((323392409/625000000 : ℝ)*X 1 0+(-169184307/1250000000 : ℝ)*X 1 1+(5992564833/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517427971/1000000000 : ℝ)*X 2 0+(1198512559/2000000000 : ℝ)*X 2 1+(-676737971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((524809241/1250000000 : ℝ)*X 0 0+(277980021/500000000 : ℝ)*X 0 1+(3177682627/10000000000 : ℝ)*X 0 2+(524809241/1250000000 : ℝ)*X 1 0+(277980021/500000000 : ℝ)*X 1 1+(3177682627/10000000000 : ℝ)*X 1 2+(524809241/1250000000 : ℝ)*X 2 0+(277980021/500000000 : ℝ)*X 2 1+(3177682627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (276200939614889443105101/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62881927/100000000000000 : ℝ)*(base1) + (670569441/50000000000000 : ℝ)*(base19) + (26864089/2000000000000 : ℝ)*(base23) + (153480059/100000000000000 : ℝ)*(upper3) + (19992899/12500000000000 : ℝ)*(upper5) + (605291200991321/100000000000000 : ℝ)*(major0) + (605291200991321/100000000000000 : ℝ)*(major1) + (605291200991321/100000000000000 : ℝ)*(major2) + (203203327691557/25000000000000 : ℝ)*(sp0) + (812816184466993/100000000000000 : ℝ)*(sp1) + (32512647296057/4000000000000 : ℝ)*(sp2) + (198881283129117/50000000000000 : ℝ)*(sp3) + (2138860787/50000000000000 : ℝ)*(sp4) + (2063102641/100000000000000 : ℝ)*(sp7) + (397764692242803/100000000000000 : ℝ)*(f.failure) + (6502540204847/800000000000 : ℝ)*(f.sum) + (469691700281633/200000000000000000000000000000 : ℝ)*base65 + (892147552281633/400000000000000000000000000000 : ℝ)*base67 + (2620705819081633/400000000000000000000000000000 : ℝ)*base69 + (934733202681633/400000000000000000000000000000 : ℝ)*base71 + (930516154281633/200000000000000000000000000000 : ℝ)*base73 + (331537178918367/400000000000000000000000000000 : ℝ)*base76 + (522439142681633/400000000000000000000000000000 : ℝ)*base77 + (645367942518367/400000000000000000000000000000 : ℝ)*base80 + (1623056368881633/200000000000000000000000000000 : ℝ)*base81 + (5167511/2000000000000000000000 : ℝ)*base89 + (5167511/2000000000000000000000 : ℝ)*base91 + (5167511/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8353089327256254844143/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (278311057/100000000000000 : ℝ)*(base1) + (414472739/100000000000000 : ℝ)*(base19) + (55750629/10000000000000 : ℝ)*(base23) + (65871741/100000000000000 : ℝ)*(upper3) + (39929453348647/6250000000000 : ℝ)*(major0) + (39929453348647/6250000000000 : ℝ)*(major1) + (39929453348647/6250000000000 : ℝ)*(major2) + (602282637/50000000000000 : ℝ)*(sp1) + (213679241/50000000000000 : ℝ)*(sp2) + (694513021/100000000000000 : ℝ)*(sp3) + (857911006850467/100000000000000 : ℝ)*(sp4) + (857909109501397/100000000000000 : ℝ)*(sp5) + (428954871837319/50000000000000 : ℝ)*(sp6) + (209915358346797/50000000000000 : ℝ)*(sp7) + (52478961189709/12500000000000 : ℝ)*(f.failure) + (85791072853941/10000000000000 : ℝ)*(f.sum) + (199221562369/12500000000000000000000000000 : ℝ)*base66 + (79605297762369/25000000000000000000000000000 : ℝ)*base68 + (118722193137369/25000000000000000000000000000 : ℝ)*base70 + (73284573012369/25000000000000000000000000000 : ℝ)*base72 + (2920178274869/12500000000000000000000000000 : ℝ)*base74 + (32972916387631/25000000000000000000000000000 : ℝ)*base75 + (2972262987631/25000000000000000000000000000 : ℝ)*base77 + (92728378687369/25000000000000000000000000000 : ℝ)*base80 + (32864466049869/12500000000000000000000000000 : ℝ)*base82 + (1550633/250000000000000000000 : ℝ)*base89 + (1550633/250000000000000000000 : ℝ)*base91 + (1550633/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1277_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (183/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13673/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1277_s1_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042423761/10000000000 : ℝ)*x 0 + (5672557361/10000000000 : ℝ)*x 1 + (1255934633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042423761/10000000000 : ℝ)^4237 ≤ (307769598637/2500000000000 : ℝ)^3213 := by
    have hnat : (2042423761 : ℕ)^4237*2500000000000^3213 ≤ 307769598637^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042423761 10000000000 307769598637 2500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5672557361/10000000000 : ℝ)^4237 ≤ (23674288713157/50000000000000 : ℝ)^3213 := by
    have hnat : (5672557361 : ℕ)^4237*50000000000000^3213 ≤ 23674288713157^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672557361 10000000000 23674288713157 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255934633/2500000000 : ℝ)^4237 ≤ (10085159652677/25000000000000 : ℝ)^3213 := by
    have hnat : (1255934633 : ℕ)^4237*25000000000000^3213 ≤ 10085159652677^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255934633 2500000000 10085159652677 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042423761/10000000000 : ℝ), (5672557361/10000000000 : ℝ), (1255934633/2500000000 : ℝ)] ![(307769598637/2500000000000 : ℝ), (23674288713157/50000000000000 : ℝ), (10085159652677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042423761/10000000000 : ℝ)|^4237 ≤ (307769598637/2500000000000 : ℝ)^3213
        have hw : |(-2042423761/10000000000 : ℝ)|=(2042423761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5672557361/10000000000 : ℝ)|^4237 ≤ (23674288713157/50000000000000 : ℝ)^3213
        have hw : |(5672557361/10000000000 : ℝ)|=(5672557361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255934633/2500000000 : ℝ)|^4237 ≤ (10085159652677/25000000000000 : ℝ)^3213
        have hw : |(1255934633/2500000000 : ℝ)|=(1255934633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s1_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412582373/10000000000 : ℝ)*x 0 + (-478132231/2000000000 : ℝ)*x 1 + (2511869431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412582373/10000000000 : ℝ)^4237 ≤ (22254054181689/50000000000000 : ℝ)^3213 := by
    have hnat : (5412582373 : ℕ)^4237*50000000000000^3213 ≤ 22254054181689^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412582373 10000000000 22254054181689 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478132231/2000000000 : ℝ)^4237 ≤ (15151249521487/100000000000000 : ℝ)^3213 := by
    have hnat : (478132231 : ℕ)^4237*100000000000000^3213 ≤ 15151249521487^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478132231 2000000000 15151249521487 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511869431/5000000000 : ℝ)^4237 ≤ (20170321052573/50000000000000 : ℝ)^3213 := by
    have hnat : (2511869431 : ℕ)^4237*50000000000000^3213 ≤ 20170321052573^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511869431 5000000000 20170321052573 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412582373/10000000000 : ℝ), (-478132231/2000000000 : ℝ), (2511869431/5000000000 : ℝ)] ![(22254054181689/50000000000000 : ℝ), (15151249521487/100000000000000 : ℝ), (20170321052573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412582373/10000000000 : ℝ)|^4237 ≤ (22254054181689/50000000000000 : ℝ)^3213
        have hw : |(5412582373/10000000000 : ℝ)|=(5412582373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478132231/2000000000 : ℝ)|^4237 ≤ (15151249521487/100000000000000 : ℝ)^3213
        have hw : |(-478132231/2000000000 : ℝ)|=(478132231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2511869431/5000000000 : ℝ)|^4237 ≤ (20170321052573/50000000000000 : ℝ)^3213
        have hw : |(2511869431/5000000000 : ℝ)|=(2511869431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s1_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412582683/10000000000 : ℝ)*x 0 + (5023738667/10000000000 : ℝ)*x 1 + (-2390660999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412582683/10000000000 : ℝ)^4237 ≤ (44508111724963/100000000000000 : ℝ)^3213 := by
    have hnat : (5412582683 : ℕ)^4237*100000000000000^3213 ≤ 44508111724963^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412582683 10000000000 44508111724963 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5023738667/10000000000 : ℝ)^4237 ≤ (40340640040251/100000000000000 : ℝ)^3213 := by
    have hnat : (5023738667 : ℕ)^4237*100000000000000^3213 ≤ 40340640040251^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023738667 10000000000 40340640040251 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2390660999/10000000000 : ℝ)^4237 ≤ (15151248217711/100000000000000 : ℝ)^3213 := by
    have hnat : (2390660999 : ℕ)^4237*100000000000000^3213 ≤ 15151248217711^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390660999 10000000000 15151248217711 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412582683/10000000000 : ℝ), (5023738667/10000000000 : ℝ), (-2390660999/10000000000 : ℝ)] ![(44508111724963/100000000000000 : ℝ), (40340640040251/100000000000000 : ℝ), (15151248217711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412582683/10000000000 : ℝ)|^4237 ≤ (44508111724963/100000000000000 : ℝ)^3213
        have hw : |(5412582683/10000000000 : ℝ)|=(5412582683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5023738667/10000000000 : ℝ)|^4237 ≤ (40340640040251/100000000000000 : ℝ)^3213
        have hw : |(5023738667/10000000000 : ℝ)|=(5023738667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2390660999/10000000000 : ℝ)|^4237 ≤ (15151248217711/100000000000000 : ℝ)^3213
        have hw : |(-2390660999/10000000000 : ℝ)|=(2390660999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s1_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151880157/5000000000 : ℝ)*x 0 + (184476641/500000000 : ℝ)*x 1 + (5015371319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151880157/5000000000 : ℝ)^4237 ≤ (8224197691283/25000000000000 : ℝ)^3213 := by
    have hnat : (2151880157 : ℕ)^4237*25000000000000^3213 ≤ 8224197691283^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151880157 5000000000 8224197691283 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184476641/500000000 : ℝ)^4237 ≤ (67127873099/250000000000 : ℝ)^3213 := by
    have hnat : (184476641 : ℕ)^4237*250000000000^3213 ≤ 67127873099^3213*500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184476641 500000000 67127873099 250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015371319/10000000000 : ℝ)^4237 ≤ (40252059976323/100000000000000 : ℝ)^3213 := by
    have hnat : (5015371319 : ℕ)^4237*100000000000000^3213 ≤ 40252059976323^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015371319 10000000000 40252059976323 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151880157/5000000000 : ℝ), (184476641/500000000 : ℝ), (5015371319/10000000000 : ℝ)] ![(8224197691283/25000000000000 : ℝ), (67127873099/250000000000 : ℝ), (40252059976323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151880157/5000000000 : ℝ)|^4237 ≤ (8224197691283/25000000000000 : ℝ)^3213
        have hw : |(2151880157/5000000000 : ℝ)|=(2151880157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184476641/500000000 : ℝ)|^4237 ≤ (67127873099/250000000000 : ℝ)^3213
        have hw : |(184476641/500000000 : ℝ)|=(184476641/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015371319/10000000000 : ℝ)|^4237 ≤ (40252059976323/100000000000000 : ℝ)^3213
        have hw : |(5015371319/10000000000 : ℝ)|=(5015371319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s1_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043093871/10000000000 : ℝ)*x 0 + (5032294373/10000000000 : ℝ)*x 1 + (2831919053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043093871/10000000000 : ℝ)^4237 ≤ (6158055311447/50000000000000 : ℝ)^3213 := by
    have hnat : (2043093871 : ℕ)^4237*50000000000000^3213 ≤ 6158055311447^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043093871 10000000000 6158055311447 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5032294373/10000000000 : ℝ)^4237 ≤ (2526953923073/6250000000000 : ℝ)^3213 := by
    have hnat : (5032294373 : ℕ)^4237*6250000000000^3213 ≤ 2526953923073^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032294373 10000000000 2526953923073 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831919053/5000000000 : ℝ)^4237 ≤ (11813156649383/25000000000000 : ℝ)^3213 := by
    have hnat : (2831919053 : ℕ)^4237*25000000000000^3213 ≤ 11813156649383^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831919053 5000000000 11813156649383 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043093871/10000000000 : ℝ), (5032294373/10000000000 : ℝ), (2831919053/5000000000 : ℝ)] ![(6158055311447/50000000000000 : ℝ), (2526953923073/6250000000000 : ℝ), (11813156649383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043093871/10000000000 : ℝ)|^4237 ≤ (6158055311447/50000000000000 : ℝ)^3213
        have hw : |(-2043093871/10000000000 : ℝ)|=(2043093871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5032294373/10000000000 : ℝ)|^4237 ≤ (2526953923073/6250000000000 : ℝ)^3213
        have hw : |(5032294373/10000000000 : ℝ)|=(5032294373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2831919053/5000000000 : ℝ)|^4237 ≤ (11813156649383/25000000000000 : ℝ)^3213
        have hw : |(2831919053/5000000000 : ℝ)|=(2831919053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s1_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5245177673/10000000000 : ℝ)*x 0 + (-875280777/5000000000 : ℝ)*x 1 + (5663838447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245177673/10000000000 : ℝ)^4237 ≤ (42701812262003/100000000000000 : ℝ)^3213 := by
    have hnat : (5245177673 : ℕ)^4237*100000000000000^3213 ≤ 42701812262003^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245177673 10000000000 42701812262003 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (875280777/5000000000 : ℝ)^4237 ≤ (1004555737377/10000000000000 : ℝ)^3213 := by
    have hnat : (875280777 : ℕ)^4237*10000000000000^3213 ≤ 1004555737377^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875280777 5000000000 1004555737377 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5663838447/10000000000 : ℝ)^4237 ≤ (23626315174569/50000000000000 : ℝ)^3213 := by
    have hnat : (5663838447 : ℕ)^4237*50000000000000^3213 ≤ 23626315174569^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663838447 10000000000 23626315174569 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245177673/10000000000 : ℝ), (-875280777/5000000000 : ℝ), (5663838447/10000000000 : ℝ)] ![(42701812262003/100000000000000 : ℝ), (1004555737377/10000000000000 : ℝ), (23626315174569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245177673/10000000000 : ℝ)|^4237 ≤ (42701812262003/100000000000000 : ℝ)^3213
        have hw : |(5245177673/10000000000 : ℝ)|=(5245177673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-875280777/5000000000 : ℝ)|^4237 ≤ (1004555737377/10000000000000 : ℝ)^3213
        have hw : |(-875280777/5000000000 : ℝ)|=(875280777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5663838447/10000000000 : ℝ)|^4237 ≤ (23626315174569/50000000000000 : ℝ)^3213
        have hw : |(5663838447/10000000000 : ℝ)|=(5663838447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s1_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1311294397/2500000000 : ℝ)*x 0 + (2831919091/5000000000 : ℝ)*x 1 + (-87528103/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311294397/2500000000 : ℝ)^4237 ≤ (42701811349461/100000000000000 : ℝ)^3213 := by
    have hnat : (1311294397 : ℕ)^4237*100000000000000^3213 ≤ 42701811349461^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311294397 2500000000 42701811349461 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2831919091/5000000000 : ℝ)^4237 ≤ (47252627433667/100000000000000 : ℝ)^3213 := by
    have hnat : (2831919091 : ℕ)^4237*100000000000000^3213 ≤ 47252627433667^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831919091 5000000000 47252627433667 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87528103/500000000 : ℝ)^4237 ≤ (5022780601427/50000000000000 : ℝ)^3213 := by
    have hnat : (87528103 : ℕ)^4237*50000000000000^3213 ≤ 5022780601427^3213*500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87528103 500000000 5022780601427 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311294397/2500000000 : ℝ), (2831919091/5000000000 : ℝ), (-87528103/500000000 : ℝ)] ![(42701811349461/100000000000000 : ℝ), (47252627433667/100000000000000 : ℝ), (5022780601427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311294397/2500000000 : ℝ)|^4237 ≤ (42701811349461/100000000000000 : ℝ)^3213
        have hw : |(1311294397/2500000000 : ℝ)|=(1311294397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2831919091/5000000000 : ℝ)|^4237 ≤ (47252627433667/100000000000000 : ℝ)^3213
        have hw : |(2831919091/5000000000 : ℝ)|=(2831919091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87528103/500000000 : ℝ)|^4237 ≤ (5022780601427/50000000000000 : ℝ)^3213
        have hw : |(-87528103/500000000 : ℝ)|=(87528103/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s1_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152564777/5000000000 : ℝ)*x 0 + (4997887881/10000000000 : ℝ)*x 1 + (463418851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152564777/5000000000 : ℝ)^4237 ≤ (32910593170813/100000000000000 : ℝ)^3213 := by
    have hnat : (2152564777 : ℕ)^4237*100000000000000^3213 ≤ 32910593170813^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152564777 5000000000 32910593170813 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4997887881/10000000000 : ℝ)^4237 ≤ (8013425082537/20000000000000 : ℝ)^3213 := by
    have hnat : (4997887881 : ℕ)^4237*20000000000000^3213 ≤ 8013425082537^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997887881 10000000000 8013425082537 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (463418851/1250000000 : ℝ)^4237 ≤ (13511140698571/50000000000000 : ℝ)^3213 := by
    have hnat : (463418851 : ℕ)^4237*50000000000000^3213 ≤ 13511140698571^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463418851 1250000000 13511140698571 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152564777/5000000000 : ℝ), (4997887881/10000000000 : ℝ), (463418851/1250000000 : ℝ)] ![(32910593170813/100000000000000 : ℝ), (8013425082537/20000000000000 : ℝ), (13511140698571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152564777/5000000000 : ℝ)|^4237 ≤ (32910593170813/100000000000000 : ℝ)^3213
        have hw : |(2152564777/5000000000 : ℝ)|=(2152564777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4997887881/10000000000 : ℝ)|^4237 ≤ (8013425082537/20000000000000 : ℝ)^3213
        have hw : |(4997887881/10000000000 : ℝ)|=(4997887881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(463418851/1250000000 : ℝ)|^4237 ≤ (13511140698571/50000000000000 : ℝ)^3213
        have hw : |(463418851/1250000000 : ℝ)|=(463418851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13673/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (183/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (3129/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4993/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13673/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (183/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13673/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (183/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13673/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (183/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13673/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (183/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13673/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (183/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13673/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (183/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (183/20000 : ℝ) ^ (1059/256 : ℝ) ≤ (92238541071/25000000000000000000 : ℝ) := by
    have hpowers : (183/20000 : ℝ)^1059 ≤ (92238541071/25000000000000000000 : ℝ)^256 := by
      have hnat : (183 : ℕ)^1059*25000000000000000000^256 ≤ 92238541071^256*20000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        183 20000 92238541071 25000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (183/20000 : ℝ)) (X := (92238541071/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13673/50000 : ℝ) ^ (1059/256 : ℝ) ≤ (468368914501816101/100000000000000000000 : ℝ) := by
    have hpowers : (13673/50000 : ℝ)^1059 ≤ (468368914501816101/100000000000000000000 : ℝ)^256 := by
      have hnat : (13673 : ℕ)^1059*100000000000000000000^256 ≤ 468368914501816101^256*50000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13673 50000 468368914501816101 100000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13673/50000 : ℝ)) (X := (468368914501816101/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000092238541071/12500000000000000000 : ℝ) ≤ (10000000017838011/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (12500000092238541071/12500000000000000000 : ℝ)^256 ≤ (10000000017838011/10000000000000000 : ℝ)^1059 := by
      have hnat : (12500000092238541071 : ℕ)^256*10000000000000000^1059 ≤ 10000000017838011^1059*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000092238541071 12500000000000000000 10000000017838011 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000017838011/10000000000000000 : ℝ)) (X := (12500000092238541071/12500000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20093673856691196077/20000000000000000000 : ℝ) ≤ (10011302191132631/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (20093673856691196077/20000000000000000000 : ℝ)^256 ≤ (10011302191132631/10000000000000000 : ℝ)^1059 := by
      have hnat : (20093673856691196077 : ℕ)^256*10000000000000000^1059 ≤ 10011302191132631^1059*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20093673856691196077 20000000000000000000 10011302191132631 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011302191132631/10000000000000000 : ℝ)) (X := (20093673856691196077/20000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50468368914501816101/50000000000000000000 : ℝ) ≤ (10022604364427251/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (50468368914501816101/50000000000000000000 : ℝ)^256 ≤ (10022604364427251/10000000000000000 : ℝ)^1059 := by
      have hnat : (50468368914501816101 : ℕ)^256*10000000000000000^1059 ≤ 10022604364427251^1059*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50468368914501816101 50000000000000000000 10022604364427251 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022604364427251/10000000000000000 : ℝ)) (X := (50468368914501816101/50000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(92238541071/25000000000000000000 : ℝ) ≤ ((264289317494347314141/264310000000000000000 : ℝ)+2*(565108664731/132155000000000 : ℝ)*(183/20000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (264289317494347314141/264310000000000000000 : ℝ)+2*(565108664731/132155000000000 : ℝ)*(183/20000 : ℝ)=(10000000017838011/10000000000000000 : ℝ) by norm_num, show 1+2*(92238541071/25000000000000000000 : ℝ)=(12500000092238541071/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(468368914501816101/100000000000000000000 : ℝ)+(92238541071/25000000000000000000 : ℝ) ≤ ((264289317494347314141/264310000000000000000 : ℝ)+(565108664731/132155000000000 : ℝ)*((13673/50000 : ℝ)+(183/20000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (264289317494347314141/264310000000000000000 : ℝ)+(565108664731/132155000000000 : ℝ)*((13673/50000 : ℝ)+(183/20000 : ℝ))=(10011302191132631/10000000000000000 : ℝ) by norm_num, show 1+(468368914501816101/100000000000000000000 : ℝ)+(92238541071/25000000000000000000 : ℝ)=(20093673856691196077/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(468368914501816101/100000000000000000000 : ℝ) ≤ ((264289317494347314141/264310000000000000000 : ℝ)+2*(565108664731/132155000000000 : ℝ)*(13673/50000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (264289317494347314141/264310000000000000000 : ℝ)+2*(565108664731/132155000000000 : ℝ)*(13673/50000 : ℝ)=(10022604364427251/10000000000000000 : ℝ) by norm_num, show 1+2*(468368914501816101/100000000000000000000 : ℝ)=(50468368914501816101/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (264289317494347314141/264310000000000000000 : ℝ)*(X 1 0+X 2 0)+(565108664731/132155000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (183/20000 : ℝ)) (hi := (13673/50000 : ℝ)) (c := (264289317494347314141/264310000000000000000 : ℝ)) (alpha := (565108664731/132155000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (264289317494347314141/264310000000000000000 : ℝ)*(X 0 1+X 2 1)+(565108664731/132155000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (183/20000 : ℝ)) (hi := (13673/50000 : ℝ)) (c := (264289317494347314141/264310000000000000000 : ℝ)) (alpha := (565108664731/132155000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (264289317494347314141/264310000000000000000 : ℝ)*(X 0 2+X 1 2)+(565108664731/132155000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (183/20000 : ℝ)) (hi := (13673/50000 : ℝ)) (c := (264289317494347314141/264310000000000000000 : ℝ)) (alpha := (565108664731/132155000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2042423761/10000000000 : ℝ)*X 0 0+(5672557361/10000000000 : ℝ)*X 0 1+(1255934633/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5412582373/10000000000 : ℝ)*X 1 0+(-478132231/2000000000 : ℝ)*X 1 1+(2511869431/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412582683/10000000000 : ℝ)*X 2 0+(5023738667/10000000000 : ℝ)*X 2 1+(-2390660999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151880157/5000000000 : ℝ)*X 0 0+(184476641/500000000 : ℝ)*X 0 1+(5015371319/10000000000 : ℝ)*X 0 2+(2151880157/5000000000 : ℝ)*X 1 0+(184476641/500000000 : ℝ)*X 1 1+(5015371319/10000000000 : ℝ)*X 1 2+(2151880157/5000000000 : ℝ)*X 2 0+(184476641/500000000 : ℝ)*X 2 1+(5015371319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2043093871/10000000000 : ℝ)*X 0 0+(5032294373/10000000000 : ℝ)*X 0 1+(2831919053/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5245177673/10000000000 : ℝ)*X 1 0+(-875280777/5000000000 : ℝ)*X 1 1+(5663838447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311294397/2500000000 : ℝ)*X 2 0+(2831919091/5000000000 : ℝ)*X 2 1+(-87528103/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2152564777/5000000000 : ℝ)*X 0 0+(4997887881/10000000000 : ℝ)*X 0 1+(463418851/1250000000 : ℝ)*X 0 2+(2152564777/5000000000 : ℝ)*X 1 0+(4997887881/10000000000 : ℝ)*X 1 1+(463418851/1250000000 : ℝ)*X 1 2+(2152564777/5000000000 : ℝ)*X 2 0+(4997887881/10000000000 : ℝ)*X 2 1+(463418851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46079996022979253552095197363/13215500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6384417/50000000000000 : ℝ)*(base1) + (850794543/100000000000000 : ℝ)*(base19) + (234767327/25000000000000 : ℝ)*(base23) + (1534139/2000000000000 : ℝ)*(upper3) + (39485451/25000000000000 : ℝ)*(upper5) + (1147759490855781/100000000000000 : ℝ)*(major0) + (1147759490855781/100000000000000 : ℝ)*(major1) + (1147759490855781/100000000000000 : ℝ)*(major2) + (770633604163157/50000000000000 : ℝ)*(sp0) + (385318113757453/25000000000000 : ℝ)*(sp1) + (770636183377523/50000000000000 : ℝ)*(sp2) + (754242709801329/100000000000000 : ℝ)*(sp3) + (3055133437/50000000000000 : ℝ)*(sp4) + (709272473/25000000000000 : ℝ)*(sp7) + (150849111932011/20000000000000 : ℝ)*(f.failure) + (770636652912177/50000000000000 : ℝ)*(f.sum) + (38921650555001/13215500000000000000000000000 : ℝ)*base66 + (79871548889926899121/26431000000000000000000000000000000 : ℝ)*base67 + (1782919932405899121/26431000000000000000000000000000000 : ℝ)*base69 + (263216452643095100879/26431000000000000000000000000000000 : ℝ)*base72 + (13844339497739/3303875000000000000000000000 : ℝ)*base73 + (269159206110206100879/26431000000000000000000000000000000 : ℝ)*base76 + (32256151252697100879/26431000000000000000000000000000000 : ℝ)*base78 + (168008051472579100879/26431000000000000000000000000000000 : ℝ)*base80 + (16819817118279/26431000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (534993/400000000000000000000 : ℝ)*base90 + (534993/400000000000000000000 : ℝ)*base92 + (534993/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72966035333743494282357264753/13215500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10545041/50000000000000 : ℝ)*(base1) + (1029492779/100000000000000 : ℝ)*(base19) + (484782467/50000000000000 : ℝ)*(base23) + (594023/400000000000 : ℝ)*(upper3) + (119460873/100000000000000 : ℝ)*(upper5) + (1179146288958237/100000000000000 : ℝ)*(major0) + (1179146288958237/100000000000000 : ℝ)*(major1) + (1179146288958237/100000000000000 : ℝ)*(major2) + (1062173879/20000000000000 : ℝ)*(sp1) + (132411409/3125000000000 : ℝ)*(sp2) + (1583421146444039/100000000000000 : ℝ)*(sp4) + (791707392495891/50000000000000 : ℝ)*(sp5) + (316683183724787/20000000000000 : ℝ)*(sp6) + (774871247430871/100000000000000 : ℝ)*(sp7) + (387435634260477/50000000000000 : ℝ)*(f.failure) + (1583421125353957/100000000000000 : ℝ)*(f.sum) + (2105865067473/26431000000000000000000000000 : ℝ)*base65 + (98292680756675470583/26431000000000000000000000000000000 : ℝ)*base68 + (195550223649399470583/26431000000000000000000000000000000 : ℝ)*base70 + (29726761761442470583/26431000000000000000000000000000000 : ℝ)*base72 + (532755538821/528620000000000000000000000 : ℝ)*base74 + (186400364121609470583/26431000000000000000000000000000000 : ℝ)*base76 + (369795468254795470583/26431000000000000000000000000000000 : ℝ)*base78 + (166512448169164470583/26431000000000000000000000000000000 : ℝ)*base80 + (4240962760697/1651937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10941849/1000000000000000000000 : ℝ)*base89 + (10941849/1000000000000000000000 : ℝ)*base91 + (10941849/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1277_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13673/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (183/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3129/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4993/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1277_s2_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044275533/5000000000 : ℝ)*x 0 + (549893877/1000000000 : ℝ)*x 1 + (2583960027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044275533/5000000000 : ℝ)^4237 ≤ (6339370843717/50000000000000 : ℝ)^3213 := by
    have hnat : (1044275533 : ℕ)^4237*50000000000000^3213 ≤ 6339370843717^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044275533 5000000000 6339370843717 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549893877/1000000000 : ℝ)^4237 ≤ (45446913958269/100000000000000 : ℝ)^3213 := by
    have hnat : (549893877 : ℕ)^4237*100000000000000^3213 ≤ 45446913958269^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549893877 1000000000 45446913958269 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583960027/5000000000 : ℝ)^4237 ≤ (20937172166373/50000000000000 : ℝ)^3213 := by
    have hnat : (2583960027 : ℕ)^4237*50000000000000^3213 ≤ 20937172166373^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583960027 5000000000 20937172166373 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044275533/5000000000 : ℝ), (549893877/1000000000 : ℝ), (2583960027/5000000000 : ℝ)] ![(6339370843717/50000000000000 : ℝ), (45446913958269/100000000000000 : ℝ), (20937172166373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044275533/5000000000 : ℝ)|^4237 ≤ (6339370843717/50000000000000 : ℝ)^3213
        have hw : |(-1044275533/5000000000 : ℝ)|=(1044275533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549893877/1000000000 : ℝ)|^4237 ≤ (45446913958269/100000000000000 : ℝ)^3213
        have hw : |(549893877/1000000000 : ℝ)|=(549893877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583960027/5000000000 : ℝ)|^4237 ≤ (20937172166373/50000000000000 : ℝ)^3213
        have hw : |(2583960027/5000000000 : ℝ)|=(2583960027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s2_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685358491/5000000000 : ℝ)*x 0 + (-56506337/250000000 : ℝ)*x 1 + (2583960527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685358491/5000000000 : ℝ)^4237 ≤ (22027344043627/50000000000000 : ℝ)^3213 := by
    have hnat : (2685358491 : ℕ)^4237*50000000000000^3213 ≤ 22027344043627^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685358491 5000000000 22027344043627 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56506337/250000000 : ℝ)^4237 ≤ (1407095687921/10000000000000 : ℝ)^3213 := by
    have hnat : (56506337 : ℕ)^4237*10000000000000^3213 ≤ 1407095687921^3213*250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56506337 250000000 1407095687921 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583960527/5000000000 : ℝ)^4237 ≤ (1046858875447/2500000000000 : ℝ)^3213 := by
    have hnat : (2583960527 : ℕ)^4237*2500000000000^3213 ≤ 1046858875447^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583960527 5000000000 1046858875447 2500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685358491/5000000000 : ℝ), (-56506337/250000000 : ℝ), (2583960527/5000000000 : ℝ)] ![(22027344043627/50000000000000 : ℝ), (1407095687921/10000000000000 : ℝ), (1046858875447/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685358491/5000000000 : ℝ)|^4237 ≤ (22027344043627/50000000000000 : ℝ)^3213
        have hw : |(2685358491/5000000000 : ℝ)|=(2685358491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56506337/250000000 : ℝ)|^4237 ≤ (1407095687921/10000000000000 : ℝ)^3213
        have hw : |(-56506337/250000000 : ℝ)|=(56506337/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583960527/5000000000 : ℝ)|^4237 ≤ (1046858875447/2500000000000 : ℝ)^3213
        have hw : |(2583960527/5000000000 : ℝ)|=(2583960527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s2_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370717563/10000000000 : ℝ)*x 0 + (20671681/40000000 : ℝ)*x 1 + (-2260253761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370717563/10000000000 : ℝ)^4237 ≤ (22027347185971/50000000000000 : ℝ)^3213 := by
    have hnat : (5370717563 : ℕ)^4237*50000000000000^3213 ≤ 22027347185971^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370717563 10000000000 22027347185971 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20671681/40000000 : ℝ)^4237 ≤ (5234293303379/12500000000000 : ℝ)^3213 := by
    have hnat : (20671681 : ℕ)^4237*12500000000000^3213 ≤ 5234293303379^3213*40000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20671681 40000000 5234293303379 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260253761/10000000000 : ℝ)^4237 ≤ (14070959186067/100000000000000 : ℝ)^3213 := by
    have hnat : (2260253761 : ℕ)^4237*100000000000000^3213 ≤ 14070959186067^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260253761 10000000000 14070959186067 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370717563/10000000000 : ℝ), (20671681/40000000 : ℝ), (-2260253761/10000000000 : ℝ)] ![(22027347185971/50000000000000 : ℝ), (5234293303379/12500000000000 : ℝ), (14070959186067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370717563/10000000000 : ℝ)|^4237 ≤ (22027347185971/50000000000000 : ℝ)^3213
        have hw : |(5370717563/10000000000 : ℝ)|=(5370717563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20671681/40000000 : ℝ)|^4237 ≤ (5234293303379/12500000000000 : ℝ)^3213
        have hw : |(20671681/40000000 : ℝ)|=(20671681/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2260253761/10000000000 : ℝ)|^4237 ≤ (14070959186067/100000000000000 : ℝ)^3213
        have hw : |(-2260253761/10000000000 : ℝ)|=(2260253761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s2_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083941251/2500000000 : ℝ)*x 0 + (2005102451/5000000000 : ℝ)*x 1 + (4686635051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083941251/2500000000 : ℝ)^4237 ≤ (33219774235013/100000000000000 : ℝ)^3213 := by
    have hnat : (1083941251 : ℕ)^4237*100000000000000^3213 ≤ 33219774235013^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083941251 2500000000 33219774235013 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005102451/5000000000 : ℝ)^4237 ≤ (3746309667617/12500000000000 : ℝ)^3213 := by
    have hnat : (2005102451 : ℕ)^4237*12500000000000^3213 ≤ 3746309667617^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005102451 5000000000 3746309667617 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4686635051/10000000000 : ℝ)^4237 ≤ (18404874206837/50000000000000 : ℝ)^3213 := by
    have hnat : (4686635051 : ℕ)^4237*50000000000000^3213 ≤ 18404874206837^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4686635051 10000000000 18404874206837 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083941251/2500000000 : ℝ), (2005102451/5000000000 : ℝ), (4686635051/10000000000 : ℝ)] ![(33219774235013/100000000000000 : ℝ), (3746309667617/12500000000000 : ℝ), (18404874206837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083941251/2500000000 : ℝ)|^4237 ≤ (33219774235013/100000000000000 : ℝ)^3213
        have hw : |(1083941251/2500000000 : ℝ)|=(1083941251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2005102451/5000000000 : ℝ)|^4237 ≤ (3746309667617/12500000000000 : ℝ)^3213
        have hw : |(2005102451/5000000000 : ℝ)|=(2005102451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4686635051/10000000000 : ℝ)|^4237 ≤ (18404874206837/50000000000000 : ℝ)^3213
        have hw : |(4686635051/10000000000 : ℝ)|=(4686635051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s2_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044319571/5000000000 : ℝ)*x 0 + (161567403/312500000 : ℝ)*x 1 + (5496680761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044319571/5000000000 : ℝ)^4237 ≤ (12679446768893/100000000000000 : ℝ)^3213 := by
    have hnat : (1044319571 : ℕ)^4237*100000000000000^3213 ≤ 12679446768893^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044319571 5000000000 12679446768893 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161567403/312500000 : ℝ)^4237 ≤ (5237280867193/12500000000000 : ℝ)^3213 := by
    have hnat : (161567403 : ℕ)^4237*12500000000000^3213 ≤ 5237280867193^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161567403 312500000 5237280867193 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496680761/10000000000 : ℝ)^4237 ≤ (2271115314397/5000000000000 : ℝ)^3213 := by
    have hnat : (5496680761 : ℕ)^4237*5000000000000^3213 ≤ 2271115314397^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496680761 10000000000 2271115314397 5000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044319571/5000000000 : ℝ), (161567403/312500000 : ℝ), (5496680761/10000000000 : ℝ)] ![(12679446768893/100000000000000 : ℝ), (5237280867193/12500000000000 : ℝ), (2271115314397/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044319571/5000000000 : ℝ)|^4237 ≤ (12679446768893/100000000000000 : ℝ)^3213
        have hw : |(-1044319571/5000000000 : ℝ)|=(1044319571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161567403/312500000 : ℝ)|^4237 ≤ (5237280867193/12500000000000 : ℝ)^3213
        have hw : |(161567403/312500000 : ℝ)|=(161567403/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496680761/10000000000 : ℝ)|^4237 ≤ (2271115314397/5000000000000 : ℝ)^3213
        have hw : |(5496680761/10000000000 : ℝ)|=(5496680761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s2_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643014079/5000000000 : ℝ)*x 0 + (-1931493081/10000000000 : ℝ)*x 1 + (5496680923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643014079/5000000000 : ℝ)^4237 ≤ (10785229412247/25000000000000 : ℝ)^3213 := by
    have hnat : (2643014079 : ℕ)^4237*25000000000000^3213 ≤ 10785229412247^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643014079 5000000000 10785229412247 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931493081/10000000000 : ℝ)^4237 ≤ (11436774276849/100000000000000 : ℝ)^3213 := by
    have hnat : (1931493081 : ℕ)^4237*100000000000000^3213 ≤ 11436774276849^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931493081 10000000000 11436774276849 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496680923/10000000000 : ℝ)^4237 ≤ (11355577013323/25000000000000 : ℝ)^3213 := by
    have hnat : (5496680923 : ℕ)^4237*25000000000000^3213 ≤ 11355577013323^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496680923 10000000000 11355577013323 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643014079/5000000000 : ℝ), (-1931493081/10000000000 : ℝ), (5496680923/10000000000 : ℝ)] ![(10785229412247/25000000000000 : ℝ), (11436774276849/100000000000000 : ℝ), (11355577013323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643014079/5000000000 : ℝ)|^4237 ≤ (10785229412247/25000000000000 : ℝ)^3213
        have hw : |(2643014079/5000000000 : ℝ)|=(2643014079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1931493081/10000000000 : ℝ)|^4237 ≤ (11436774276849/100000000000000 : ℝ)^3213
        have hw : |(-1931493081/10000000000 : ℝ)|=(1931493081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496680923/10000000000 : ℝ)|^4237 ≤ (11355577013323/25000000000000 : ℝ)^3213
        have hw : |(5496680923/10000000000 : ℝ)|=(5496680923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s2_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286028349/10000000000 : ℝ)*x 0 + (5496680771/10000000000 : ℝ)*x 1 + (-1931493031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286028349/10000000000 : ℝ)^4237 ≤ (43140919704599/100000000000000 : ℝ)^3213 := by
    have hnat : (5286028349 : ℕ)^4237*100000000000000^3213 ≤ 43140919704599^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286028349 10000000000 43140919704599 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496680771/10000000000 : ℝ)^4237 ≤ (2838894149807/6250000000000 : ℝ)^3213 := by
    have hnat : (5496680771 : ℕ)^4237*6250000000000^3213 ≤ 2838894149807^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496680771 10000000000 2838894149807 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1931493031/10000000000 : ℝ)^4237 ≤ (11436773886433/100000000000000 : ℝ)^3213 := by
    have hnat : (1931493031 : ℕ)^4237*100000000000000^3213 ≤ 11436773886433^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931493031 10000000000 11436773886433 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286028349/10000000000 : ℝ), (5496680771/10000000000 : ℝ), (-1931493031/10000000000 : ℝ)] ![(43140919704599/100000000000000 : ℝ), (2838894149807/6250000000000 : ℝ), (11436773886433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286028349/10000000000 : ℝ)|^4237 ≤ (43140919704599/100000000000000 : ℝ)^3213
        have hw : |(5286028349/10000000000 : ℝ)|=(5286028349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496680771/10000000000 : ℝ)|^4237 ≤ (2838894149807/6250000000000 : ℝ)^3213
        have hw : |(5496680771/10000000000 : ℝ)|=(5496680771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1931493031/10000000000 : ℝ)|^4237 ≤ (11436773886433/100000000000000 : ℝ)^3213
        have hw : |(-1931493031/10000000000 : ℝ)|=(1931493031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s2_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335945447/10000000000 : ℝ)*x 0 + (2341031699/5000000000 : ℝ)*x 1 + (2007411407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335945447/10000000000 : ℝ)^4237 ≤ (33221597381641/100000000000000 : ℝ)^3213 := by
    have hnat : (4335945447 : ℕ)^4237*100000000000000^3213 ≤ 33221597381641^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335945447 10000000000 33221597381641 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2341031699/5000000000 : ℝ)^4237 ≤ (36762405478269/100000000000000 : ℝ)^3213 := by
    have hnat : (2341031699 : ℕ)^4237*100000000000000^3213 ≤ 36762405478269^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341031699 5000000000 36762405478269 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007411407/5000000000 : ℝ)^4237 ≤ (30015997120777/100000000000000 : ℝ)^3213 := by
    have hnat : (2007411407 : ℕ)^4237*100000000000000^3213 ≤ 30015997120777^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007411407 5000000000 30015997120777 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335945447/10000000000 : ℝ), (2341031699/5000000000 : ℝ), (2007411407/5000000000 : ℝ)] ![(33221597381641/100000000000000 : ℝ), (36762405478269/100000000000000 : ℝ), (30015997120777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335945447/10000000000 : ℝ)|^4237 ≤ (33221597381641/100000000000000 : ℝ)^3213
        have hw : |(4335945447/10000000000 : ℝ)|=(4335945447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2341031699/5000000000 : ℝ)|^4237 ≤ (36762405478269/100000000000000 : ℝ)^3213
        have hw : |(2341031699/5000000000 : ℝ)|=(2341031699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2007411407/5000000000 : ℝ)|^4237 ≤ (30015997120777/100000000000000 : ℝ)^3213
        have hw : |(2007411407/5000000000 : ℝ)|=(2007411407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4993/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3129/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16387/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4993/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3129/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4993/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3129/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4993/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3129/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4993/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3129/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4993/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3129/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4993/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3129/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3129/50000 : ℝ) ^ (1059/256 : ℝ) ≤ (1050007519666979/100000000000000000000 : ℝ) := by
    have hpowers : (3129/50000 : ℝ)^1059 ≤ (1050007519666979/100000000000000000000 : ℝ)^256 := by
      have hnat : (3129 : ℕ)^1059*100000000000000000000^256 ≤ 1050007519666979^256*50000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3129 50000 1050007519666979 100000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3129/50000 : ℝ)) (X := (1050007519666979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (4993/25000 : ℝ) ^ (1059/256 : ℝ) ≤ (127655855176013509/100000000000000000000 : ℝ) := by
    have hpowers : (4993/25000 : ℝ)^1059 ≤ (127655855176013509/100000000000000000000 : ℝ)^256 := by
      have hnat : (4993 : ℕ)^1059*100000000000000000000^256 ≤ 127655855176013509^256*25000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4993 25000 127655855176013509 100000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4993/25000 : ℝ)) (X := (127655855176013509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001050007519666979/50000000000000000000 : ℝ) ≤ (100000507648319/100000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (50001050007519666979/50000000000000000000 : ℝ)^256 ≤ (100000507648319/100000000000000 : ℝ)^1059 := by
      have hnat : (50001050007519666979 : ℕ)^256*100000000000000^1059 ≤ 100000507648319^1059*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001050007519666979 50000000000000000000 100000507648319 100000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100000507648319/100000000000000 : ℝ)) (X := (50001050007519666979/50000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12516088232836960061/12500000000000000000 : ℝ) ≤ (50015548930681/50000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (12516088232836960061/12500000000000000000 : ℝ)^256 ≤ (50015548930681/50000000000000 : ℝ)^1059 := by
      have hnat : (12516088232836960061 : ℕ)^256*50000000000000^1059 ≤ 50015548930681^1059*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12516088232836960061 12500000000000000000 50015548930681 50000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50015548930681/50000000000000 : ℝ)) (X := (12516088232836960061/12500000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50127655855176013509/50000000000000000000 : ℝ) ≤ (20012337614881/20000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (50127655855176013509/50000000000000000000 : ℝ)^256 ≤ (20012337614881/20000000000000 : ℝ)^1059 := by
      have hnat : (50127655855176013509 : ℕ)^256*20000000000000^1059 ≤ 20012337614881^1059*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50127655855176013509 50000000000000000000 20012337614881 20000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20012337614881/20000000000000 : ℝ)) (X := (50127655855176013509/50000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1050007519666979/100000000000000000000 : ℝ) ≤ ((685512047391300289/685700000000000000 : ℝ)+2*(30590213043/13714000000000 : ℝ)*(3129/50000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (685512047391300289/685700000000000000 : ℝ)+2*(30590213043/13714000000000 : ℝ)*(3129/50000 : ℝ)=(100000507648319/100000000000000 : ℝ) by norm_num, show 1+2*(1050007519666979/100000000000000000000 : ℝ)=(50001050007519666979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(127655855176013509/100000000000000000000 : ℝ)+(1050007519666979/100000000000000000000 : ℝ) ≤ ((685512047391300289/685700000000000000 : ℝ)+(30590213043/13714000000000 : ℝ)*((4993/25000 : ℝ)+(3129/50000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (685512047391300289/685700000000000000 : ℝ)+(30590213043/13714000000000 : ℝ)*((4993/25000 : ℝ)+(3129/50000 : ℝ))=(50015548930681/50000000000000 : ℝ) by norm_num, show 1+(127655855176013509/100000000000000000000 : ℝ)+(1050007519666979/100000000000000000000 : ℝ)=(12516088232836960061/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(127655855176013509/100000000000000000000 : ℝ) ≤ ((685512047391300289/685700000000000000 : ℝ)+2*(30590213043/13714000000000 : ℝ)*(4993/25000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (685512047391300289/685700000000000000 : ℝ)+2*(30590213043/13714000000000 : ℝ)*(4993/25000 : ℝ)=(20012337614881/20000000000000 : ℝ) by norm_num, show 1+2*(127655855176013509/100000000000000000000 : ℝ)=(50127655855176013509/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (685512047391300289/685700000000000000 : ℝ)*(X 1 0+X 2 0)+(30590213043/13714000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (3129/50000 : ℝ)) (hi := (4993/25000 : ℝ)) (c := (685512047391300289/685700000000000000 : ℝ)) (alpha := (30590213043/13714000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (685512047391300289/685700000000000000 : ℝ)*(X 0 1+X 2 1)+(30590213043/13714000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (3129/50000 : ℝ)) (hi := (4993/25000 : ℝ)) (c := (685512047391300289/685700000000000000 : ℝ)) (alpha := (30590213043/13714000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (685512047391300289/685700000000000000 : ℝ)*(X 0 2+X 1 2)+(30590213043/13714000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (3129/50000 : ℝ)) (hi := (4993/25000 : ℝ)) (c := (685512047391300289/685700000000000000 : ℝ)) (alpha := (30590213043/13714000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1044275533/5000000000 : ℝ)*X 0 0+(549893877/1000000000 : ℝ)*X 0 1+(2583960027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685358491/5000000000 : ℝ)*X 1 0+(-56506337/250000000 : ℝ)*X 1 1+(2583960527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370717563/10000000000 : ℝ)*X 2 0+(20671681/40000000 : ℝ)*X 2 1+(-2260253761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083941251/2500000000 : ℝ)*X 0 0+(2005102451/5000000000 : ℝ)*X 0 1+(4686635051/10000000000 : ℝ)*X 0 2+(1083941251/2500000000 : ℝ)*X 1 0+(2005102451/5000000000 : ℝ)*X 1 1+(4686635051/10000000000 : ℝ)*X 1 2+(1083941251/2500000000 : ℝ)*X 2 0+(2005102451/5000000000 : ℝ)*X 2 1+(4686635051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1044319571/5000000000 : ℝ)*X 0 0+(161567403/312500000 : ℝ)*X 0 1+(5496680761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643014079/5000000000 : ℝ)*X 1 0+(-1931493081/10000000000 : ℝ)*X 1 1+(5496680923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5286028349/10000000000 : ℝ)*X 2 0+(5496680771/10000000000 : ℝ)*X 2 1+(-1931493031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4335945447/10000000000 : ℝ)*X 0 0+(2341031699/5000000000 : ℝ)*X 0 1+(2007411407/5000000000 : ℝ)*X 0 2+(4335945447/10000000000 : ℝ)*X 1 0+(2341031699/5000000000 : ℝ)*X 1 1+(2007411407/5000000000 : ℝ)*X 1 2+(4335945447/10000000000 : ℝ)*X 2 0+(2341031699/5000000000 : ℝ)*X 2 1+(2007411407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (521627243145402029401911/1071406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (952055769/100000000000000 : ℝ)*(base19) + (303192769/25000000000000 : ℝ)*(base23) + (376483761/100000000000000 : ℝ)*(upper3) + (35497339/100000000000000 : ℝ)*(upper4) + (206816763/100000000000000 : ℝ)*(upper5) + (562421926219643/25000000000000 : ℝ)*(major0) + (562421926219643/25000000000000 : ℝ)*(major1) + (562421926219643/25000000000000 : ℝ)*(major2) + (188811898991643/6250000000000 : ℝ)*(sp0) + (755250290612351/25000000000000 : ℝ)*(sp1) + (188812556358381/6250000000000 : ℝ)*(sp2) + (92397506892321/6250000000000 : ℝ)*(sp3) + (2346127777/20000000000000 : ℝ)*(sp4) + (3292186521/25000000000000 : ℝ)*(sp7) + (1478373279023221/100000000000000 : ℝ)*(f.failure) + (3021002114505173/100000000000000 : ℝ)*(f.sum) + (22720284005581/3428500000000000000000000000 : ℝ)*base65 + (44494237340406827/17142500000000000000000000000000 : ℝ)*base67 + (100468879320594327/17142500000000000000000000000000 : ℝ)*base69 + (272298074253976827/17142500000000000000000000000000 : ℝ)*base71 + (116049493017/428562500000000000000000000 : ℝ)*base73 + (35190364883413173/17142500000000000000000000000000 : ℝ)*base76 + (242049287535876827/17142500000000000000000000000000 : ℝ)*base77 + (293297786168006827/17142500000000000000000000000000 : ℝ)*base79 + (187754637027/428562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5705777/2000000000000000000000 : ℝ)*base89 + (5705777/2000000000000000000000 : ℝ)*base91 + (5705777/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40938858292764025610918163/17142500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (430160119/100000000000000 : ℝ)*(base19) + (135777659/20000000000000 : ℝ)*(base23) + (12522237/12500000000000 : ℝ)*(upper3) + (9288081/20000000000000 : ℝ)*(lower4) + (1140318101643137/50000000000000 : ℝ)*(major0) + (1140318101643137/50000000000000 : ℝ)*(major1) + (1140318101643137/50000000000000 : ℝ)*(major2) + (2126101/48828125000 : ℝ)*(sp1) + (7488411919/100000000000000 : ℝ)*(sp2) + (127951917/100000000000000 : ℝ)*(sp3) + (1531280682987561/50000000000000 : ℝ)*(sp4) + (1531278290780077/50000000000000 : ℝ)*(sp5) + (3062553198674907/100000000000000 : ℝ)*(sp6) + (1498710833040503/100000000000000 : ℝ)*(sp7) + (74935548049621/5000000000000 : ℝ)*(f.failure) + (1531280682987561/50000000000000 : ℝ)*(f.sum) + (731062871589/274280000000000000000000000 : ℝ)*base66 + (158448283340116593/34285000000000000000000000000000 : ℝ)*base67 + (219021018718981593/34285000000000000000000000000000 : ℝ)*base69 + (227225709750071593/34285000000000000000000000000000 : ℝ)*base71 + (1075168878111/3428500000000000000000000000 : ℝ)*base73 + (478644726624761593/34285000000000000000000000000000 : ℝ)*base75 + (355296405943551593/34285000000000000000000000000000 : ℝ)*base77 + (372529592305641593/34285000000000000000000000000000 : ℝ)*base79 + (1760264152639/6857000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (877423/100000000000000000000 : ℝ)*base90 + (877423/100000000000000000000 : ℝ)*base92 + (877423/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1277_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4993/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3129/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16387/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1277_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16387/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1277_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1277_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1277_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16387/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1277_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
