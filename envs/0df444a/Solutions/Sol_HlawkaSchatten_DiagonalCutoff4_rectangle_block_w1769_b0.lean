-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1769_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:30:53.52048+00:00
-- url     : https://prove2.me/submissions/a24ac21f-9e73-4315-a23b-45a470a678cd

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
theorem support_rectangle_w1769_s0_0 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-545838689/5000000000 : ℝ)*x 0 + (5576488109/10000000000 : ℝ)*x 1 + (500354751/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545838689/5000000000 : ℝ)^6079 ≤ (6970106747713/100000000000000 : ℝ)^5055 := by
    have hnat : (545838689 : ℕ)^6079*100000000000000^5055 ≤ 6970106747713^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545838689 5000000000 6970106747713 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5576488109/10000000000 : ℝ)^6079 ≤ (24771405810873/50000000000000 : ℝ)^5055 := by
    have hnat : (5576488109 : ℕ)^6079*50000000000000^5055 ≤ 24771405810873^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576488109 10000000000 24771405810873 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500354751/1000000000 : ℝ)^6079 ≤ (169871412531/390625000000 : ℝ)^5055 := by
    have hnat : (500354751 : ℕ)^6079*390625000000^5055 ≤ 169871412531^5055*1000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500354751 1000000000 169871412531 390625000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545838689/5000000000 : ℝ), (5576488109/10000000000 : ℝ), (500354751/1000000000 : ℝ)] ![(6970106747713/100000000000000 : ℝ), (24771405810873/50000000000000 : ℝ), (169871412531/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545838689/5000000000 : ℝ)|^6079 ≤ (6970106747713/100000000000000 : ℝ)^5055
        have hw : |(-545838689/5000000000 : ℝ)|=(545838689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5576488109/10000000000 : ℝ)|^6079 ≤ (24771405810873/50000000000000 : ℝ)^5055
        have hw : |(5576488109/10000000000 : ℝ)|=(5576488109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500354751/1000000000 : ℝ)|^6079 ≤ (169871412531/390625000000 : ℝ)^5055
        have hw : |(500354751/1000000000 : ℝ)|=(500354751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s0_1 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337684409/2500000000 : ℝ)*x 0 + (-698226751/5000000000 : ℝ)*x 1 + (5003546923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337684409/2500000000 : ℝ)^6079 ≤ (47140908318337/100000000000000 : ℝ)^5055 := by
    have hnat : (1337684409 : ℕ)^6079*100000000000000^5055 ≤ 47140908318337^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337684409 2500000000 47140908318337 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698226751/5000000000 : ℝ)^6079 ≤ (2343004048909/25000000000000 : ℝ)^5055 := by
    have hnat : (698226751 : ℕ)^6079*25000000000000^5055 ≤ 2343004048909^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698226751 5000000000 2343004048909 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5003546923/10000000000 : ℝ)^6079 ≤ (43487075472699/100000000000000 : ℝ)^5055 := by
    have hnat : (5003546923 : ℕ)^6079*100000000000000^5055 ≤ 43487075472699^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003546923 10000000000 43487075472699 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337684409/2500000000 : ℝ), (-698226751/5000000000 : ℝ), (5003546923/10000000000 : ℝ)] ![(47140908318337/100000000000000 : ℝ), (2343004048909/25000000000000 : ℝ), (43487075472699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337684409/2500000000 : ℝ)|^6079 ≤ (47140908318337/100000000000000 : ℝ)^5055
        have hw : |(1337684409/2500000000 : ℝ)|=(1337684409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698226751/5000000000 : ℝ)|^6079 ≤ (2343004048909/25000000000000 : ℝ)^5055
        have hw : |(-698226751/5000000000 : ℝ)|=(698226751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5003546923/10000000000 : ℝ)|^6079 ≤ (43487075472699/100000000000000 : ℝ)^5055
        have hw : |(5003546923/10000000000 : ℝ)|=(5003546923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s0_2 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675366883/5000000000 : ℝ)*x 0 + (2501774777/5000000000 : ℝ)*x 1 + (-55858207/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675366883/5000000000 : ℝ)^6079 ≤ (47140867316227/100000000000000 : ℝ)^5055 := by
    have hnat : (2675366883 : ℕ)^6079*100000000000000^5055 ≤ 47140867316227^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675366883 5000000000 47140867316227 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2501774777/5000000000 : ℝ)^6079 ≤ (67948598393/156250000000 : ℝ)^5055 := by
    have hnat : (2501774777 : ℕ)^6079*156250000000^5055 ≤ 67948598393^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501774777 5000000000 67948598393 156250000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55858207/400000000 : ℝ)^6079 ≤ (1874405939623/20000000000000 : ℝ)^5055 := by
    have hnat : (55858207 : ℕ)^6079*20000000000000^5055 ≤ 1874405939623^5055*400000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55858207 400000000 1874405939623 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675366883/5000000000 : ℝ), (2501774777/5000000000 : ℝ), (-55858207/400000000 : ℝ)] ![(47140867316227/100000000000000 : ℝ), (67948598393/156250000000 : ℝ), (1874405939623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675366883/5000000000 : ℝ)|^6079 ≤ (47140867316227/100000000000000 : ℝ)^5055
        have hw : |(2675366883/5000000000 : ℝ)|=(2675366883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2501774777/5000000000 : ℝ)|^6079 ≤ (67948598393/156250000000 : ℝ)^5055
        have hw : |(2501774777/5000000000 : ℝ)|=(2501774777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55858207/400000000 : ℝ)|^6079 ≤ (1874405939623/20000000000000 : ℝ)^5055
        have hw : |(-55858207/400000000 : ℝ)|=(55858207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s0_3 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3950272781/10000000000 : ℝ)*x 0 + (3000619673/10000000000 : ℝ)*x 1 + (5029577963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3950272781/10000000000 : ℝ)^6079 ≤ (32727674333823/100000000000000 : ℝ)^5055 := by
    have hnat : (3950272781 : ℕ)^6079*100000000000000^5055 ≤ 32727674333823^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3950272781 10000000000 32727674333823 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3000619673/10000000000 : ℝ)^6079 ≤ (2351303445949/10000000000000 : ℝ)^5055 := by
    have hnat : (3000619673 : ℕ)^6079*10000000000000^5055 ≤ 2351303445949^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3000619673 10000000000 2351303445949 10000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5029577963/10000000000 : ℝ)^6079 ≤ (437592911919/1000000000000 : ℝ)^5055 := by
    have hnat : (5029577963 : ℕ)^6079*1000000000000^5055 ≤ 437592911919^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5029577963 10000000000 437592911919 1000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3950272781/10000000000 : ℝ), (3000619673/10000000000 : ℝ), (5029577963/10000000000 : ℝ)] ![(32727674333823/100000000000000 : ℝ), (2351303445949/10000000000000 : ℝ), (437592911919/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3950272781/10000000000 : ℝ)|^6079 ≤ (32727674333823/100000000000000 : ℝ)^5055
        have hw : |(3950272781/10000000000 : ℝ)|=(3950272781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3000619673/10000000000 : ℝ)|^6079 ≤ (2351303445949/10000000000000 : ℝ)^5055
        have hw : |(3000619673/10000000000 : ℝ)|=(3000619673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5029577963/10000000000 : ℝ)|^6079 ≤ (437592911919/1000000000000 : ℝ)^5055
        have hw : |(5029577963/10000000000 : ℝ)|=(5029577963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s0_4 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-68293947/625000000 : ℝ)*x 0 + (5017716271/10000000000 : ℝ)*x 1 + (2780941007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68293947/625000000 : ℝ)^6079 ≤ (6977983534847/100000000000000 : ℝ)^5055 := by
    have hnat : (68293947 : ℕ)^6079*100000000000000^5055 ≤ 6977983534847^5055*625000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68293947 625000000 6977983534847 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5017716271/10000000000 : ℝ)^6079 ≤ (43635213832387/100000000000000 : ℝ)^5055 := by
    have hnat : (5017716271 : ℕ)^6079*100000000000000^5055 ≤ 43635213832387^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017716271 10000000000 43635213832387 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2780941007/5000000000 : ℝ)^6079 ≤ (24693401308943/50000000000000 : ℝ)^5055 := by
    have hnat : (2780941007 : ℕ)^6079*50000000000000^5055 ≤ 24693401308943^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2780941007 5000000000 24693401308943 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68293947/625000000 : ℝ), (5017716271/10000000000 : ℝ), (2780941007/5000000000 : ℝ)] ![(6977983534847/100000000000000 : ℝ), (43635213832387/100000000000000 : ℝ), (24693401308943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68293947/625000000 : ℝ)|^6079 ≤ (6977983534847/100000000000000 : ℝ)^5055
        have hw : |(-68293947/625000000 : ℝ)|=(68293947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5017716271/10000000000 : ℝ)|^6079 ≤ (43635213832387/100000000000000 : ℝ)^5055
        have hw : |(5017716271/10000000000 : ℝ)|=(5017716271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2780941007/5000000000 : ℝ)|^6079 ≤ (24693401308943/50000000000000 : ℝ)^5055
        have hw : |(2780941007/5000000000 : ℝ)|=(2780941007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s0_5 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199289063/10000000000 : ℝ)*x 0 + (-104765099/1250000000 : ℝ)*x 1 + (695235251/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199289063/10000000000 : ℝ)^6079 ≤ (22770483394779/50000000000000 : ℝ)^5055 := by
    have hnat : (5199289063 : ℕ)^6079*50000000000000^5055 ≤ 22770483394779^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199289063 10000000000 22770483394779 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104765099/1250000000 : ℝ)^6079 ≤ (39626801881/781250000000 : ℝ)^5055 := by
    have hnat : (104765099 : ℕ)^6079*781250000000^5055 ≤ 39626801881^5055*1250000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104765099 1250000000 39626801881 781250000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695235251/1250000000 : ℝ)^6079 ≤ (49386802553817/100000000000000 : ℝ)^5055 := by
    have hnat : (695235251 : ℕ)^6079*100000000000000^5055 ≤ 49386802553817^5055*1250000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695235251 1250000000 49386802553817 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199289063/10000000000 : ℝ), (-104765099/1250000000 : ℝ), (695235251/1250000000 : ℝ)] ![(22770483394779/50000000000000 : ℝ), (39626801881/781250000000 : ℝ), (49386802553817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199289063/10000000000 : ℝ)|^6079 ≤ (22770483394779/50000000000000 : ℝ)^5055
        have hw : |(5199289063/10000000000 : ℝ)|=(5199289063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104765099/1250000000 : ℝ)|^6079 ≤ (39626801881/781250000000 : ℝ)^5055
        have hw : |(-104765099/1250000000 : ℝ)|=(104765099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(695235251/1250000000 : ℝ)|^6079 ≤ (49386802553817/100000000000000 : ℝ)^5055
        have hw : |(695235251/1250000000 : ℝ)|=(695235251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s0_6 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199289411/10000000000 : ℝ)*x 0 + (2780940937/5000000000 : ℝ)*x 1 + (-167624097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199289411/10000000000 : ℝ)^6079 ≤ (45540970455187/100000000000000 : ℝ)^5055 := by
    have hnat : (5199289411 : ℕ)^6079*100000000000000^5055 ≤ 45540970455187^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199289411 10000000000 45540970455187 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2780940937/5000000000 : ℝ)^6079 ≤ (49386801122931/100000000000000 : ℝ)^5055 := by
    have hnat : (2780940937 : ℕ)^6079*100000000000000^5055 ≤ 49386801122931^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2780940937 5000000000 49386801122931 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167624097/2000000000 : ℝ)^6079 ≤ (5072228406467/100000000000000 : ℝ)^5055 := by
    have hnat : (167624097 : ℕ)^6079*100000000000000^5055 ≤ 5072228406467^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167624097 2000000000 5072228406467 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199289411/10000000000 : ℝ), (2780940937/5000000000 : ℝ), (-167624097/2000000000 : ℝ)] ![(45540970455187/100000000000000 : ℝ), (49386801122931/100000000000000 : ℝ), (5072228406467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199289411/10000000000 : ℝ)|^6079 ≤ (45540970455187/100000000000000 : ℝ)^5055
        have hw : |(5199289411/10000000000 : ℝ)|=(5199289411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2780940937/5000000000 : ℝ)|^6079 ≤ (49386801122931/100000000000000 : ℝ)^5055
        have hw : |(2780940937/5000000000 : ℝ)|=(2780940937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-167624097/2000000000 : ℝ)|^6079 ≤ (5072228406467/100000000000000 : ℝ)^5055
        have hw : |(-167624097/2000000000 : ℝ)|=(167624097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s0_7 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3953901139/10000000000 : ℝ)*x 0 + (995881223/2000000000 : ℝ)*x 1 + (610468537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3953901139/10000000000 : ℝ)^6079 ≤ (32763827768661/100000000000000 : ℝ)^5055 := by
    have hnat : (3953901139 : ℕ)^6079*100000000000000^5055 ≤ 32763827768661^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3953901139 10000000000 32763827768661 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995881223/2000000000 : ℝ)^6079 ≤ (10808720701233/25000000000000 : ℝ)^5055 := by
    have hnat : (995881223 : ℕ)^6079*25000000000000^5055 ≤ 10808720701233^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995881223 2000000000 10808720701233 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610468537/2000000000 : ℝ)^6079 ≤ (24001289409469/100000000000000 : ℝ)^5055 := by
    have hnat : (610468537 : ℕ)^6079*100000000000000^5055 ≤ 24001289409469^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610468537 2000000000 24001289409469 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3953901139/10000000000 : ℝ), (995881223/2000000000 : ℝ), (610468537/2000000000 : ℝ)] ![(32763827768661/100000000000000 : ℝ), (10808720701233/25000000000000 : ℝ), (24001289409469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3953901139/10000000000 : ℝ)|^6079 ≤ (32763827768661/100000000000000 : ℝ)^5055
        have hw : |(3953901139/10000000000 : ℝ)|=(3953901139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(995881223/2000000000 : ℝ)|^6079 ≤ (10808720701233/25000000000000 : ℝ)^5055
        have hw : |(995881223/2000000000 : ℝ)|=(995881223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(610468537/2000000000 : ℝ)|^6079 ≤ (24001289409469/100000000000000 : ℝ)^5055
        have hw : |(610468537/2000000000 : ℝ)|=(610468537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1769_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3701/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19849/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (6063/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^6063 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^6063*1^1024 ≤ 0^1024*1^6063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 6063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (6063/1024 : ℝ) ≤ (440390178076322619/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^6063 ≤ (440390178076322619/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^6063*100000000000000000000^1024 ≤ 440390178076322619^1024*5^6063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 440390178076322619 100000000000000000000 6063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (440390178076322619/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^6063 := by
      have hnat : (1 : ℕ)^1024*1^6063 ≤ 1^6063*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100440390178076322619/100000000000000000000 : ℝ) ≤ (3202375782141/3200000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (100440390178076322619/100000000000000000000 : ℝ)^1024 ≤ (3202375782141/3200000000000 : ℝ)^6063 := by
      have hnat : (100440390178076322619 : ℕ)^1024*3200000000000^6063 ≤ 3202375782141^6063*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100440390178076322619 100000000000000000000 3202375782141 3200000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3202375782141/3200000000000 : ℝ)) (X := (100440390178076322619/100000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50440390178076322619/50000000000000000000 : ℝ) ≤ (1602375782141/1600000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (50440390178076322619/50000000000000000000 : ℝ)^1024 ≤ (1602375782141/1600000000000 : ℝ)^6063 := by
      have hnat : (50440390178076322619 : ℕ)^1024*1600000000000^6063 ≤ 1602375782141^6063*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50440390178076322619 50000000000000000000 1602375782141 1600000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1602375782141/1600000000000 : ℝ)) (X := (50440390178076322619/50000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2375782141/1280000000000 : ℝ)*(0 : ℝ))^(6063/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2375782141/1280000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(440390178076322619/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2375782141/1280000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(6063/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2375782141/1280000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(3202375782141/3200000000000 : ℝ) by norm_num, show 1+(440390178076322619/100000000000000000000 : ℝ)+(0 : ℝ)=(100440390178076322619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(440390178076322619/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2375782141/1280000000000 : ℝ)*(2/5 : ℝ))^(6063/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2375782141/1280000000000 : ℝ)*(2/5 : ℝ)=(1602375782141/1600000000000 : ℝ) by norm_num, show 1+2*(440390178076322619/100000000000000000000 : ℝ)=(50440390178076322619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2375782141/1280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2375782141/1280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2375782141/1280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2375782141/1280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2375782141/1280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2375782141/1280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-545838689/5000000000 : ℝ)*X 0 0+(5576488109/10000000000 : ℝ)*X 0 1+(500354751/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337684409/2500000000 : ℝ)*X 1 0+(-698226751/5000000000 : ℝ)*X 1 1+(5003546923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675366883/5000000000 : ℝ)*X 2 0+(2501774777/5000000000 : ℝ)*X 2 1+(-55858207/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3950272781/10000000000 : ℝ)*X 0 0+(3000619673/10000000000 : ℝ)*X 0 1+(5029577963/10000000000 : ℝ)*X 0 2+(3950272781/10000000000 : ℝ)*X 1 0+(3000619673/10000000000 : ℝ)*X 1 1+(5029577963/10000000000 : ℝ)*X 1 2+(3950272781/10000000000 : ℝ)*X 2 0+(3000619673/10000000000 : ℝ)*X 2 1+(5029577963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-68293947/625000000 : ℝ)*X 0 0+(5017716271/10000000000 : ℝ)*X 0 1+(2780941007/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5199289063/10000000000 : ℝ)*X 1 0+(-104765099/1250000000 : ℝ)*X 1 1+(695235251/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199289411/10000000000 : ℝ)*X 2 0+(2780940937/5000000000 : ℝ)*X 2 1+(-167624097/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3953901139/10000000000 : ℝ)*X 0 0+(995881223/2000000000 : ℝ)*X 0 1+(610468537/2000000000 : ℝ)*X 0 2+(3953901139/10000000000 : ℝ)*X 1 0+(995881223/2000000000 : ℝ)*X 1 1+(610468537/2000000000 : ℝ)*X 1 2+(3953901139/10000000000 : ℝ)*X 2 0+(995881223/2000000000 : ℝ)*X 2 1+(610468537/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (199886099641110574041/64000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135905343/50000000000000 : ℝ)*(base1) + (54558227/100000000000000 : ℝ)*(base16) + (1073806293/100000000000000 : ℝ)*(base19) + (113661233/100000000000000 : ℝ)*(base59) + (22613693/10000000000000 : ℝ)*(upper3) + (1119126448291247/100000000000000 : ℝ)*(major0) + (1119126448291247/100000000000000 : ℝ)*(major1) + (1119126448291247/100000000000000 : ℝ)*(major2) + (1745388168866499/100000000000000 : ℝ)*(sp0) + (872693784023579/50000000000000 : ℝ)*(sp1) + (1745385926149417/100000000000000 : ℝ)*(sp2) + (492863824252781/100000000000000 : ℝ)*(sp3) + (159871173/20000000000000 : ℝ)*(sp4) + (2770262261/100000000000000 : ℝ)*(sp6) + (123216024015867/25000000000000 : ℝ)*(f.failure) + (872694348205839/50000000000000 : ℝ)*(f.sum) + (52678483149/64000000000000000000000000 : ℝ)*base66 + (83217846761/25600000000000000000000000 : ℝ)*base68 + (73313097843/128000000000000000000000000 : ℝ)*base69 + (154283242729/25600000000000000000000000 : ℝ)*base72 + (89977168819/64000000000000000000000000 : ℝ)*base73 + (132384852109/128000000000000000000000000 : ℝ)*base76 + (100008534377/25600000000000000000000000 : ℝ)*base78 + (702569531533/128000000000000000000000000 : ℝ)*base80 + (5656425003/2560000000000000000000000 : ℝ)*base81 + (24127177/2500000000000000000000 : ℝ)*base89 + (24127177/2500000000000000000000 : ℝ)*base91 + (24127177/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114745251016770093567/32000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159975839/50000000000000 : ℝ)*(base19) + (479351947/100000000000000 : ℝ)*(base23) + (7176761/6250000000000 : ℝ)*(base32) + (84577613/100000000000000 : ℝ)*(upper3) + (45151317/100000000000000 : ℝ)*(upper5) + (589149808199097/50000000000000 : ℝ)*(major0) + (589149808199097/50000000000000 : ℝ)*(major1) + (589149808199097/50000000000000 : ℝ)*(major2) + (201735887/20000000000000 : ℝ)*(sp1) + (2258389637/100000000000000 : ℝ)*(sp2) + (918837555618647/50000000000000 : ℝ)*(sp4) + (91883689130309/5000000000000 : ℝ)*(sp5) + (183767237349571/10000000000000 : ℝ)*(sp6) + (259461943602303/50000000000000 : ℝ)*(sp7) + (518924002032781/100000000000000 : ℝ)*(f.failure) + (918837555618647/50000000000000 : ℝ)*(f.sum) + (9455466159/6400000000000000000000000 : ℝ)*base66 + (28751160619/64000000000000000000000000 : ℝ)*base68 + (445574544213/64000000000000000000000000 : ℝ)*base69 + (125169167701/64000000000000000000000000 : ℝ)*base71 + (84078745643/32000000000000000000000000 : ℝ)*base74 + (804319643157/64000000000000000000000000 : ℝ)*base75 + (48487456427/64000000000000000000000000 : ℝ)*base78 + (49136110703/12800000000000000000000000 : ℝ)*base80 + (98608405557/32000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (89715889/10000000000000000000000 : ℝ)*base90 + (89715889/10000000000000000000000 : ℝ)*base92 + (89715889/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1769_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3701/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19849/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1769_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1769_s1_0 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-280881231/2500000000 : ℝ)*x 0 + (218961531/400000000 : ℝ)*x 1 + (1016895969/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280881231/2500000000 : ℝ)^6079 ≤ (7215353717443/100000000000000 : ℝ)^5055 := by
    have hnat : (280881231 : ℕ)^6079*100000000000000^5055 ≤ 7215353717443^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280881231 2500000000 7215353717443 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218961531/400000000 : ℝ)^6079 ≤ (6056286502483/12500000000000 : ℝ)^5055 := by
    have hnat : (218961531 : ℕ)^6079*12500000000000^5055 ≤ 6056286502483^5055*400000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218961531 400000000 6056286502483 12500000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016895969/2000000000 : ℝ)^6079 ≤ (2216717712049/5000000000000 : ℝ)^5055 := by
    have hnat : (1016895969 : ℕ)^6079*5000000000000^5055 ≤ 2216717712049^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016895969 2000000000 2216717712049 5000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-280881231/2500000000 : ℝ), (218961531/400000000 : ℝ), (1016895969/2000000000 : ℝ)] ![(7215353717443/100000000000000 : ℝ), (6056286502483/12500000000000 : ℝ), (2216717712049/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-280881231/2500000000 : ℝ)|^6079 ≤ (7215353717443/100000000000000 : ℝ)^5055
        have hw : |(-280881231/2500000000 : ℝ)|=(280881231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218961531/400000000 : ℝ)|^6079 ≤ (6056286502483/12500000000000 : ℝ)^5055
        have hw : |(218961531/400000000 : ℝ)|=(218961531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016895969/2000000000 : ℝ)|^6079 ≤ (2216717712049/5000000000000 : ℝ)^5055
        have hw : |(1016895969/2000000000 : ℝ)|=(1016895969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s1_1 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1330897939/2500000000 : ℝ)*x 0 + (-1326732107/10000000000 : ℝ)*x 1 + (1271120069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1330897939/2500000000 : ℝ)^6079 ≤ (23426724736977/50000000000000 : ℝ)^5055 := by
    have hnat : (1330897939 : ℕ)^6079*50000000000000^5055 ≤ 23426724736977^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330897939 2500000000 23426724736977 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1326732107/10000000000 : ℝ)^6079 ≤ (4406095877513/50000000000000 : ℝ)^5055 := by
    have hnat : (1326732107 : ℕ)^6079*50000000000000^5055 ≤ 4406095877513^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326732107 10000000000 4406095877513 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271120069/2500000000 : ℝ)^6079 ≤ (22167179380197/50000000000000 : ℝ)^5055 := by
    have hnat : (1271120069 : ℕ)^6079*50000000000000^5055 ≤ 22167179380197^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271120069 2500000000 22167179380197 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1330897939/2500000000 : ℝ), (-1326732107/10000000000 : ℝ), (1271120069/2500000000 : ℝ)] ![(23426724736977/50000000000000 : ℝ), (4406095877513/50000000000000 : ℝ), (22167179380197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1330897939/2500000000 : ℝ)|^6079 ≤ (23426724736977/50000000000000 : ℝ)^5055
        have hw : |(1330897939/2500000000 : ℝ)|=(1330897939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1326732107/10000000000 : ℝ)|^6079 ≤ (4406095877513/50000000000000 : ℝ)^5055
        have hw : |(-1326732107/10000000000 : ℝ)|=(1326732107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271120069/2500000000 : ℝ)|^6079 ≤ (22167179380197/50000000000000 : ℝ)^5055
        have hw : |(1271120069/2500000000 : ℝ)|=(1271120069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s1_2 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2661796297/5000000000 : ℝ)*x 0 + (635559917/1250000000 : ℝ)*x 1 + (-1326732229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2661796297/5000000000 : ℝ)^6079 ≤ (9370691668661/20000000000000 : ℝ)^5055 := by
    have hnat : (2661796297 : ℕ)^6079*20000000000000^5055 ≤ 9370691668661^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2661796297 5000000000 9370691668661 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635559917/1250000000 : ℝ)^6079 ≤ (11083587225917/25000000000000 : ℝ)^5055 := by
    have hnat : (635559917 : ℕ)^6079*25000000000000^5055 ≤ 11083587225917^5055*1250000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635559917 1250000000 11083587225917 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1326732229/10000000000 : ℝ)^6079 ≤ (8812192729503/100000000000000 : ℝ)^5055 := by
    have hnat : (1326732229 : ℕ)^6079*100000000000000^5055 ≤ 8812192729503^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326732229 10000000000 8812192729503 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2661796297/5000000000 : ℝ), (635559917/1250000000 : ℝ), (-1326732229/10000000000 : ℝ)] ![(9370691668661/20000000000000 : ℝ), (11083587225917/25000000000000 : ℝ), (8812192729503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2661796297/5000000000 : ℝ)|^6079 ≤ (9370691668661/20000000000000 : ℝ)^5055
        have hw : |(2661796297/5000000000 : ℝ)|=(2661796297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635559917/1250000000 : ℝ)|^6079 ≤ (11083587225917/25000000000000 : ℝ)^5055
        have hw : |(635559917/1250000000 : ℝ)|=(635559917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1326732229/10000000000 : ℝ)|^6079 ≤ (8812192729503/100000000000000 : ℝ)^5055
        have hw : |(-1326732229/10000000000 : ℝ)|=(1326732229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s1_3 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (796605817/2000000000 : ℝ)*x 0 + (166154827/500000000 : ℝ)*x 1 + (4702653019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796605817/2000000000 : ℝ)^6079 ≤ (33054305586439/100000000000000 : ℝ)^5055 := by
    have hnat : (796605817 : ℕ)^6079*100000000000000^5055 ≤ 33054305586439^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796605817 2000000000 33054305586439 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166154827/500000000 : ℝ)^6079 ≤ (26584047029271/100000000000000 : ℝ)^5055 := by
    have hnat : (166154827 : ℕ)^6079*100000000000000^5055 ≤ 26584047029271^5055*500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166154827 500000000 26584047029271 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4702653019/10000000000 : ℝ)^6079 ≤ (5045205921163/12500000000000 : ℝ)^5055 := by
    have hnat : (4702653019 : ℕ)^6079*12500000000000^5055 ≤ 5045205921163^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4702653019 10000000000 5045205921163 12500000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796605817/2000000000 : ℝ), (166154827/500000000 : ℝ), (4702653019/10000000000 : ℝ)] ![(33054305586439/100000000000000 : ℝ), (26584047029271/100000000000000 : ℝ), (5045205921163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796605817/2000000000 : ℝ)|^6079 ≤ (33054305586439/100000000000000 : ℝ)^5055
        have hw : |(796605817/2000000000 : ℝ)|=(796605817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166154827/500000000 : ℝ)|^6079 ≤ (26584047029271/100000000000000 : ℝ)^5055
        have hw : |(166154827/500000000 : ℝ)|=(166154827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4702653019/10000000000 : ℝ)|^6079 ≤ (5045205921163/12500000000000 : ℝ)^5055
        have hw : |(4702653019/10000000000 : ℝ)|=(4702653019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s1_4 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-561922887/5000000000 : ℝ)*x 0 + (2545525931/5000000000 : ℝ)*x 1 + (136683233/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (561922887/5000000000 : ℝ)^6079 ≤ (1804457928221/25000000000000 : ℝ)^5055 := by
    have hnat : (561922887 : ℕ)^6079*25000000000000^5055 ≤ 1804457928221^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561922887 5000000000 1804457928221 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545525931/5000000000 : ℝ)^6079 ≤ (277520478967/625000000000 : ℝ)^5055 := by
    have hnat : (2545525931 : ℕ)^6079*625000000000^5055 ≤ 277520478967^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545525931 5000000000 277520478967 625000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136683233/250000000 : ℝ)^6079 ≤ (48378891643779/100000000000000 : ℝ)^5055 := by
    have hnat : (136683233 : ℕ)^6079*100000000000000^5055 ≤ 48378891643779^5055*250000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136683233 250000000 48378891643779 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-561922887/5000000000 : ℝ), (2545525931/5000000000 : ℝ), (136683233/250000000 : ℝ)] ![(1804457928221/25000000000000 : ℝ), (277520478967/625000000000 : ℝ), (48378891643779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-561922887/5000000000 : ℝ)|^6079 ≤ (1804457928221/25000000000000 : ℝ)^5055
        have hw : |(-561922887/5000000000 : ℝ)|=(561922887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2545525931/5000000000 : ℝ)|^6079 ≤ (277520478967/625000000000 : ℝ)^5055
        have hw : |(2545525931/5000000000 : ℝ)|=(2545525931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136683233/250000000 : ℝ)|^6079 ≤ (48378891643779/100000000000000 : ℝ)^5055
        have hw : |(136683233/250000000 : ℝ)|=(136683233/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s1_5 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5220988797/10000000000 : ℝ)*x 0 + (-943882677/10000000000 : ℝ)*x 1 + (68341613/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5220988797/10000000000 : ℝ)^6079 ≤ (45769635647089/100000000000000 : ℝ)^5055 := by
    have hnat : (5220988797 : ℕ)^6079*100000000000000^5055 ≤ 45769635647089^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220988797 10000000000 45769635647089 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943882677/10000000000 : ℝ)^6079 ≤ (292573783707/5000000000000 : ℝ)^5055 := by
    have hnat : (943882677 : ℕ)^6079*5000000000000^5055 ≤ 292573783707^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943882677 10000000000 292573783707 5000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68341613/125000000 : ℝ)^6079 ≤ (9675777732847/20000000000000 : ℝ)^5055 := by
    have hnat : (68341613 : ℕ)^6079*20000000000000^5055 ≤ 9675777732847^5055*125000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68341613 125000000 9675777732847 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5220988797/10000000000 : ℝ), (-943882677/10000000000 : ℝ), (68341613/125000000 : ℝ)] ![(45769635647089/100000000000000 : ℝ), (292573783707/5000000000000 : ℝ), (9675777732847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5220988797/10000000000 : ℝ)|^6079 ≤ (45769635647089/100000000000000 : ℝ)^5055
        have hw : |(5220988797/10000000000 : ℝ)|=(5220988797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-943882677/10000000000 : ℝ)|^6079 ≤ (292573783707/5000000000000 : ℝ)^5055
        have hw : |(-943882677/10000000000 : ℝ)|=(943882677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68341613/125000000 : ℝ)|^6079 ≤ (9675777732847/20000000000000 : ℝ)^5055
        have hw : |(68341613/125000000 : ℝ)|=(68341613/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s1_6 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044197809/2000000000 : ℝ)*x 0 + (5467328977/10000000000 : ℝ)*x 1 + (-58992651/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044197809/2000000000 : ℝ)^6079 ≤ (45769638261581/100000000000000 : ℝ)^5055 := by
    have hnat : (1044197809 : ℕ)^6079*100000000000000^5055 ≤ 45769638261581^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044197809 2000000000 45769638261581 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467328977/10000000000 : ℝ)^6079 ≤ (24189443996919/50000000000000 : ℝ)^5055 := by
    have hnat : (5467328977 : ℕ)^6079*50000000000000^5055 ≤ 24189443996919^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467328977 10000000000 24189443996919 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58992651/625000000 : ℝ)^6079 ≤ (5851473728337/100000000000000 : ℝ)^5055 := by
    have hnat : (58992651 : ℕ)^6079*100000000000000^5055 ≤ 5851473728337^5055*625000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58992651 625000000 5851473728337 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044197809/2000000000 : ℝ), (5467328977/10000000000 : ℝ), (-58992651/625000000 : ℝ)] ![(45769638261581/100000000000000 : ℝ), (24189443996919/50000000000000 : ℝ), (5851473728337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044197809/2000000000 : ℝ)|^6079 ≤ (45769638261581/100000000000000 : ℝ)^5055
        have hw : |(1044197809/2000000000 : ℝ)|=(1044197809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467328977/10000000000 : ℝ)|^6079 ≤ (24189443996919/50000000000000 : ℝ)^5055
        have hw : |(5467328977/10000000000 : ℝ)|=(5467328977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58992651/625000000 : ℝ)|^6079 ≤ (5851473728337/100000000000000 : ℝ)^5055
        have hw : |(-58992651/625000000 : ℝ)|=(58992651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s1_7 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (498020779/1250000000 : ℝ)*x 0 + (4679377277/10000000000 : ℝ)*x 1 + (334685903/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498020779/1250000000 : ℝ)^6079 ≤ (33065654511043/100000000000000 : ℝ)^5055 := by
    have hnat : (498020779 : ℕ)^6079*100000000000000^5055 ≤ 33065654511043^5055*1250000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498020779 1250000000 33065654511043 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4679377277/10000000000 : ℝ)^6079 ≤ (40121530647/100000000000 : ℝ)^5055 := by
    have hnat : (4679377277 : ℕ)^6079*100000000000^5055 ≤ 40121530647^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4679377277 10000000000 40121530647 100000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334685903/1000000000 : ℝ)^6079 ≤ (5362562966731/20000000000000 : ℝ)^5055 := by
    have hnat : (334685903 : ℕ)^6079*20000000000000^5055 ≤ 5362562966731^5055*1000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334685903 1000000000 5362562966731 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(498020779/1250000000 : ℝ), (4679377277/10000000000 : ℝ), (334685903/1000000000 : ℝ)] ![(33065654511043/100000000000000 : ℝ), (40121530647/100000000000 : ℝ), (5362562966731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(498020779/1250000000 : ℝ)|^6079 ≤ (33065654511043/100000000000000 : ℝ)^5055
        have hw : |(498020779/1250000000 : ℝ)|=(498020779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4679377277/10000000000 : ℝ)|^6079 ≤ (40121530647/100000000000 : ℝ)^5055
        have hw : |(4679377277/10000000000 : ℝ)|=(4679377277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(334685903/1000000000 : ℝ)|^6079 ≤ (5362562966731/20000000000000 : ℝ)^5055
        have hw : |(334685903/1000000000 : ℝ)|=(334685903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1769_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19849/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (288/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17641/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19849/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19849/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19849/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19849/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19849/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19849/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3701/50000 : ℝ) ^ (6063/1024 : ℝ) ≤ (20208344594771/100000000000000000000 : ℝ) := by
    have hpowers : (3701/50000 : ℝ)^6063 ≤ (20208344594771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3701 : ℕ)^6063*100000000000000000000^1024 ≤ 20208344594771^1024*50000^6063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3701 50000 20208344594771 100000000000000000000 6063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3701/50000 : ℝ)) (X := (20208344594771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19849/100000 : ℝ) ^ (6063/1024 : ℝ) ≤ (6949951308265161/100000000000000000000 : ℝ) := by
    have hpowers : (19849/100000 : ℝ)^6063 ≤ (6949951308265161/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19849 : ℕ)^6063*100000000000000000000^1024 ≤ 6949951308265161^1024*100000^6063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19849 100000 6949951308265161 100000000000000000000 6063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19849/100000 : ℝ)) (X := (6949951308265161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000020208344594771/50000000000000000000 : ℝ) ≤ (2000000136522127/2000000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (50000020208344594771/50000000000000000000 : ℝ)^1024 ≤ (2000000136522127/2000000000000000 : ℝ)^6063 := by
      have hnat : (50000020208344594771 : ℕ)^1024*2000000000000000^6063 ≤ 2000000136522127^6063*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000020208344594771 50000000000000000000 2000000136522127 2000000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000136522127/2000000000000000 : ℝ)) (X := (50000020208344594771/50000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25001742539913214983/25000000000000000000 : ℝ) ≤ (10000117717907953/10000000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (25001742539913214983/25000000000000000000 : ℝ)^1024 ≤ (10000117717907953/10000000000000000 : ℝ)^6063 := by
      have hnat : (25001742539913214983 : ℕ)^1024*10000000000000000^6063 ≤ 10000117717907953^6063*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001742539913214983 25000000000000000000 10000117717907953 10000000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000117717907953/10000000000000000 : ℝ)) (X := (25001742539913214983/25000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50006949951308265161/50000000000000000000 : ℝ) ≤ (10000234753205271/10000000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (50006949951308265161/50000000000000000000 : ℝ)^1024 ≤ (10000234753205271/10000000000000000 : ℝ)^6063 := by
      have hnat : (50006949951308265161 : ℕ)^1024*10000000000000000^6063 ≤ 10000234753205271^6063*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006949951308265161 50000000000000000000 10000234753205271 10000000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000234753205271/10000000000000000 : ℝ)) (X := (50006949951308265161/50000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20208344594771/100000000000000000000 : ℝ) ≤ ((124468275905913078173/124470000000000000000 : ℝ)+2*(58517648659/622350000000000 : ℝ)*(3701/50000 : ℝ))^(6063/1024 : ℝ) := by
    rw [show (124468275905913078173/124470000000000000000 : ℝ)+2*(58517648659/622350000000000 : ℝ)*(3701/50000 : ℝ)=(2000000136522127/2000000000000000 : ℝ) by norm_num, show 1+2*(20208344594771/100000000000000000000 : ℝ)=(50000020208344594771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6949951308265161/100000000000000000000 : ℝ)+(20208344594771/100000000000000000000 : ℝ) ≤ ((124468275905913078173/124470000000000000000 : ℝ)+(58517648659/622350000000000 : ℝ)*((19849/100000 : ℝ)+(3701/50000 : ℝ)))^(6063/1024 : ℝ) := by
    rw [show (124468275905913078173/124470000000000000000 : ℝ)+(58517648659/622350000000000 : ℝ)*((19849/100000 : ℝ)+(3701/50000 : ℝ))=(10000117717907953/10000000000000000 : ℝ) by norm_num, show 1+(6949951308265161/100000000000000000000 : ℝ)+(20208344594771/100000000000000000000 : ℝ)=(25001742539913214983/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6949951308265161/100000000000000000000 : ℝ) ≤ ((124468275905913078173/124470000000000000000 : ℝ)+2*(58517648659/622350000000000 : ℝ)*(19849/100000 : ℝ))^(6063/1024 : ℝ) := by
    rw [show (124468275905913078173/124470000000000000000 : ℝ)+2*(58517648659/622350000000000 : ℝ)*(19849/100000 : ℝ)=(10000234753205271/10000000000000000 : ℝ) by norm_num, show 1+2*(6949951308265161/100000000000000000000 : ℝ)=(50006949951308265161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (124468275905913078173/124470000000000000000 : ℝ)*(X 1 0+X 2 0)+(58517648659/622350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (3701/50000 : ℝ)) (hi := (19849/100000 : ℝ)) (c := (124468275905913078173/124470000000000000000 : ℝ)) (alpha := (58517648659/622350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (124468275905913078173/124470000000000000000 : ℝ)*(X 0 1+X 2 1)+(58517648659/622350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (3701/50000 : ℝ)) (hi := (19849/100000 : ℝ)) (c := (124468275905913078173/124470000000000000000 : ℝ)) (alpha := (58517648659/622350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (124468275905913078173/124470000000000000000 : ℝ)*(X 0 2+X 1 2)+(58517648659/622350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (3701/50000 : ℝ)) (hi := (19849/100000 : ℝ)) (c := (124468275905913078173/124470000000000000000 : ℝ)) (alpha := (58517648659/622350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-280881231/2500000000 : ℝ)*X 0 0+(218961531/400000000 : ℝ)*X 0 1+(1016895969/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1330897939/2500000000 : ℝ)*X 1 0+(-1326732107/10000000000 : ℝ)*X 1 1+(1271120069/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2661796297/5000000000 : ℝ)*X 2 0+(635559917/1250000000 : ℝ)*X 2 1+(-1326732229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((796605817/2000000000 : ℝ)*X 0 0+(166154827/500000000 : ℝ)*X 0 1+(4702653019/10000000000 : ℝ)*X 0 2+(796605817/2000000000 : ℝ)*X 1 0+(166154827/500000000 : ℝ)*X 1 1+(4702653019/10000000000 : ℝ)*X 1 2+(796605817/2000000000 : ℝ)*X 2 0+(166154827/500000000 : ℝ)*X 2 1+(4702653019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-561922887/5000000000 : ℝ)*X 0 0+(2545525931/5000000000 : ℝ)*X 0 1+(136683233/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5220988797/10000000000 : ℝ)*X 1 0+(-943882677/10000000000 : ℝ)*X 1 1+(68341613/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1044197809/2000000000 : ℝ)*X 2 0+(5467328977/10000000000 : ℝ)*X 2 1+(-58992651/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((498020779/1250000000 : ℝ)*X 0 0+(4679377277/10000000000 : ℝ)*X 0 1+(334685903/1000000000 : ℝ)*X 0 2+(498020779/1250000000 : ℝ)*X 1 0+(4679377277/10000000000 : ℝ)*X 1 1+(334685903/1000000000 : ℝ)*X 1 2+(498020779/1250000000 : ℝ)*X 2 0+(4679377277/10000000000 : ℝ)*X 2 1+(334685903/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7670725878849265569606720127/691500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1255292639/100000000000000 : ℝ)*(base19) + (328222797/20000000000000 : ℝ)*(base23) + (60303361/20000000000000 : ℝ)*(upper3) + (9721487/100000000000000 : ℝ)*(upper4) + (33034411/12500000000000 : ℝ)*(upper5) + (1645955426102901/100000000000000 : ℝ)*(major0) + (1645955426102901/100000000000000 : ℝ)*(major1) + (1645955426102901/100000000000000 : ℝ)*(major2) + (16043871204423/625000000000 : ℝ)*(sp0) + (1283514634390777/50000000000000 : ℝ)*(sp1) + (160439305185013/6250000000000 : ℝ)*(sp2) + (90609376534009/12500000000000 : ℝ)*(sp3) + (11131366513/100000000000000 : ℝ)*(sp4) + (1236524223/25000000000000 : ℝ)*(sp7) + (181219989592241/25000000000000 : ℝ)*(f.failure) + (1283515262037097/50000000000000 : ℝ)*(f.sum) + (2116763894737/648281250000000000000000000 : ℝ)*base66 + (16775150717772293291/4149000000000000000000000000000000 : ℝ)*base67 + (28087035275790293291/4149000000000000000000000000000000 : ℝ)*base69 + (7593286268790293291/4149000000000000000000000000000000 : ℝ)*base71 + (20027278844891/5186250000000000000000000000 : ℝ)*base74 + (131661836334293291/4149000000000000000000000000000000 : ℝ)*base75 + (19765494978318293291/4149000000000000000000000000000000 : ℝ)*base77 + (11519559800154293291/4149000000000000000000000000000000 : ℝ)*base79 + (11793661348493/10372500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11958629/2500000000000000000000 : ℝ)*base90 + (11958629/2500000000000000000000 : ℝ)*base92 + (11958629/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181332151481080009571199127/25931250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98253483/12500000000000 : ℝ)*(base19) + (519835091/50000000000000 : ℝ)*(base23) + (52570609/50000000000000 : ℝ)*(upper3) + (41570369/100000000000000 : ℝ)*(lower4) + (53993001/50000000000000 : ℝ)*(upper5) + (21300451752533/1250000000000 : ℝ)*(major0) + (21300451752533/1250000000000 : ℝ)*(major1) + (21300451752533/1250000000000 : ℝ)*(major2) + (461608327/10000000000000 : ℝ)*(sp1) + (7047475299/100000000000000 : ℝ)*(sp2) + (332201662563409/12500000000000 : ℝ)*(sp4) + (1328803949198069/50000000000000 : ℝ)*(sp5) + (265760521336179/10000000000000 : ℝ)*(sp6) + (750458746804531/100000000000000 : ℝ)*(sp7) + (750458746804531/100000000000000 : ℝ)*(f.failure) + (332201662563409/12500000000000 : ℝ)*(f.sum) + (4325330522113/1555875000000000000000000000 : ℝ)*base66 + (311215407024550291/155587500000000000000000000000000 : ℝ)*base68 + (2067969026703212791/155587500000000000000000000000000 : ℝ)*base70 + (1009554769423412791/155587500000000000000000000000000 : ℝ)*base72 + (34300685377267/12447000000000000000000000000 : ℝ)*base73 + (1184389948015712791/155587500000000000000000000000000 : ℝ)*base76 + (919055440777787791/155587500000000000000000000000000 : ℝ)*base78 + (19857560449675291/155587500000000000000000000000000 : ℝ)*base80 + (78278422286189/12447000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (106533361/10000000000000000000000 : ℝ)*base89 + (106533361/10000000000000000000000 : ℝ)*base91 + (106533361/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1769_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19849/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (288/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17641/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1769_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1769_s2_0 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-35123843/312500000 : ℝ)*x 0 + (5472625889/10000000000 : ℝ)*x 1 + (2542795403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35123843/312500000 : ℝ)^6079 ≤ (1804684231391/25000000000000 : ℝ)^5055 := by
    have hnat : (35123843 : ℕ)^6079*25000000000000^5055 ≤ 1804684231391^5055*312500000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35123843 312500000 1804684231391 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472625889/10000000000 : ℝ)^6079 ≤ (24217629580047/50000000000000 : ℝ)^5055 := by
    have hnat : (5472625889 : ℕ)^6079*50000000000000^5055 ≤ 24217629580047^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472625889 10000000000 24217629580047 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542795403/5000000000 : ℝ)^6079 ≤ (11086500975339/25000000000000 : ℝ)^5055 := by
    have hnat : (2542795403 : ℕ)^6079*25000000000000^5055 ≤ 11086500975339^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542795403 5000000000 11086500975339 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35123843/312500000 : ℝ), (5472625889/10000000000 : ℝ), (2542795403/5000000000 : ℝ)] ![(1804684231391/25000000000000 : ℝ), (24217629580047/50000000000000 : ℝ), (11086500975339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35123843/312500000 : ℝ)|^6079 ≤ (1804684231391/25000000000000 : ℝ)^5055
        have hw : |(-35123843/312500000 : ℝ)|=(35123843/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472625889/10000000000 : ℝ)|^6079 ≤ (24217629580047/50000000000000 : ℝ)^5055
        have hw : |(5472625889/10000000000 : ℝ)|=(5472625889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542795403/5000000000 : ℝ)|^6079 ≤ (11086500975339/25000000000000 : ℝ)^5055
        have hw : |(2542795403/5000000000 : ℝ)|=(2542795403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s2_1 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5323195479/10000000000 : ℝ)*x 0 + (-662899603/5000000000 : ℝ)*x 1 + (635698851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5323195479/10000000000 : ℝ)^6079 ≤ (46849255329329/100000000000000 : ℝ)^5055 := by
    have hnat : (5323195479 : ℕ)^6079*100000000000000^5055 ≤ 46849255329329^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5323195479 10000000000 46849255329329 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (662899603/5000000000 : ℝ)^6079 ≤ (1760948145031/20000000000000 : ℝ)^5055 := by
    have hnat : (662899603 : ℕ)^6079*20000000000000^5055 ≤ 1760948145031^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662899603 5000000000 1760948145031 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635698851/1250000000 : ℝ)^6079 ≤ (44346003922329/100000000000000 : ℝ)^5055 := by
    have hnat : (635698851 : ℕ)^6079*100000000000000^5055 ≤ 44346003922329^5055*1250000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635698851 1250000000 44346003922329 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5323195479/10000000000 : ℝ), (-662899603/5000000000 : ℝ), (635698851/1250000000 : ℝ)] ![(46849255329329/100000000000000 : ℝ), (1760948145031/20000000000000 : ℝ), (44346003922329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5323195479/10000000000 : ℝ)|^6079 ≤ (46849255329329/100000000000000 : ℝ)^5055
        have hw : |(5323195479/10000000000 : ℝ)|=(5323195479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-662899603/5000000000 : ℝ)|^6079 ≤ (1760948145031/20000000000000 : ℝ)^5055
        have hw : |(-662899603/5000000000 : ℝ)|=(662899603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635698851/1250000000 : ℝ)|^6079 ≤ (44346003922329/100000000000000 : ℝ)^5055
        have hw : |(635698851/1250000000 : ℝ)|=(635698851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s2_2 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5323195469/10000000000 : ℝ)*x 0 + (1271397703/2500000000 : ℝ)*x 1 + (-265159843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5323195469/10000000000 : ℝ)^6079 ≤ (46849255223491/100000000000000 : ℝ)^5055 := by
    have hnat : (5323195469 : ℕ)^6079*100000000000000^5055 ≤ 46849255223491^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5323195469 10000000000 46849255223491 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271397703/2500000000 : ℝ)^6079 ≤ (22173001982137/50000000000000 : ℝ)^5055 := by
    have hnat : (1271397703 : ℕ)^6079*50000000000000^5055 ≤ 22173001982137^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271397703 2500000000 22173001982137 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265159843/2000000000 : ℝ)^6079 ≤ (1100592599629/12500000000000 : ℝ)^5055 := by
    have hnat : (265159843 : ℕ)^6079*12500000000000^5055 ≤ 1100592599629^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265159843 2000000000 1100592599629 12500000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5323195469/10000000000 : ℝ), (1271397703/2500000000 : ℝ), (-265159843/2000000000 : ℝ)] ![(46849255223491/100000000000000 : ℝ), (22173001982137/50000000000000 : ℝ), (1100592599629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5323195469/10000000000 : ℝ)|^6079 ≤ (46849255223491/100000000000000 : ℝ)^5055
        have hw : |(5323195469/10000000000 : ℝ)|=(5323195469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271397703/2500000000 : ℝ)|^6079 ≤ (22173001982137/50000000000000 : ℝ)^5055
        have hw : |(1271397703/2500000000 : ℝ)|=(1271397703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265159843/2000000000 : ℝ)|^6079 ≤ (1100592599629/12500000000000 : ℝ)^5055
        have hw : |(-265159843/2000000000 : ℝ)|=(265159843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s2_3 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1991695553/5000000000 : ℝ)*x 0 + (103985719/312500000 : ℝ)*x 1 + (58726969/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991695553/5000000000 : ℝ)^6079 ≤ (16528959273851/50000000000000 : ℝ)^5055 := by
    have hnat : (1991695553 : ℕ)^6079*50000000000000^5055 ≤ 16528959273851^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991695553 5000000000 16528959273851 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103985719/312500000 : ℝ)^6079 ≤ (2662682923049/10000000000000 : ℝ)^5055 := by
    have hnat : (103985719 : ℕ)^6079*10000000000000^5055 ≤ 2662682923049^5055*312500000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103985719 312500000 2662682923049 10000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58726969/125000000 : ℝ)^6079 ≤ (1259851631217/3125000000000 : ℝ)^5055 := by
    have hnat : (58726969 : ℕ)^6079*3125000000000^5055 ≤ 1259851631217^5055*125000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58726969 125000000 1259851631217 3125000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1991695553/5000000000 : ℝ), (103985719/312500000 : ℝ), (58726969/125000000 : ℝ)] ![(16528959273851/50000000000000 : ℝ), (2662682923049/10000000000000 : ℝ), (1259851631217/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1991695553/5000000000 : ℝ)|^6079 ≤ (16528959273851/50000000000000 : ℝ)^5055
        have hw : |(1991695553/5000000000 : ℝ)|=(1991695553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103985719/312500000 : ℝ)|^6079 ≤ (2662682923049/10000000000000 : ℝ)^5055
        have hw : |(103985719/312500000 : ℝ)|=(103985719/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58726969/125000000 : ℝ)|^6079 ≤ (1259851631217/3125000000000 : ℝ)^5055
        have hw : |(58726969/125000000 : ℝ)|=(58726969/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s2_4 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-281069509/2500000000 : ℝ)*x 0 + (1018415681/2000000000 : ℝ)*x 1 + (1093200739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281069509/2500000000 : ℝ)^6079 ≤ (722117039441/10000000000000 : ℝ)^5055 := by
    have hnat : (281069509 : ℕ)^6079*10000000000000^5055 ≤ 722117039441^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281069509 2500000000 722117039441 10000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018415681/2000000000 : ℝ)^6079 ≤ (22207021938633/50000000000000 : ℝ)^5055 := by
    have hnat : (1018415681 : ℕ)^6079*50000000000000^5055 ≤ 22207021938633^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018415681 2000000000 22207021938633 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093200739/2000000000 : ℝ)^6079 ≤ (9672957143021/20000000000000 : ℝ)^5055 := by
    have hnat : (1093200739 : ℕ)^6079*20000000000000^5055 ≤ 9672957143021^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093200739 2000000000 9672957143021 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-281069509/2500000000 : ℝ), (1018415681/2000000000 : ℝ), (1093200739/2000000000 : ℝ)] ![(722117039441/10000000000000 : ℝ), (22207021938633/50000000000000 : ℝ), (9672957143021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-281069509/2500000000 : ℝ)|^6079 ≤ (722117039441/10000000000000 : ℝ)^5055
        have hw : |(-281069509/2500000000 : ℝ)|=(281069509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018415681/2000000000 : ℝ)|^6079 ≤ (22207021938633/50000000000000 : ℝ)^5055
        have hw : |(1018415681/2000000000 : ℝ)|=(1018415681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093200739/2000000000 : ℝ)|^6079 ≤ (9672957143021/20000000000000 : ℝ)^5055
        have hw : |(1093200739/2000000000 : ℝ)|=(1093200739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s2_5 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2610631519/5000000000 : ℝ)*x 0 + (-945386327/10000000000 : ℝ)*x 1 + (1093200739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2610631519/5000000000 : ℝ)^6079 ≤ (22886263397703/50000000000000 : ℝ)^5055 := by
    have hnat : (2610631519 : ℕ)^6079*50000000000000^5055 ≤ 22886263397703^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610631519 5000000000 22886263397703 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945386327/10000000000 : ℝ)^6079 ≤ (1172537493939/20000000000000 : ℝ)^5055 := by
    have hnat : (945386327 : ℕ)^6079*20000000000000^5055 ≤ 1172537493939^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945386327 10000000000 1172537493939 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093200739/2000000000 : ℝ)^6079 ≤ (9672957143021/20000000000000 : ℝ)^5055 := by
    have hnat : (1093200739 : ℕ)^6079*20000000000000^5055 ≤ 9672957143021^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093200739 2000000000 9672957143021 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2610631519/5000000000 : ℝ), (-945386327/10000000000 : ℝ), (1093200739/2000000000 : ℝ)] ![(22886263397703/50000000000000 : ℝ), (1172537493939/20000000000000 : ℝ), (9672957143021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2610631519/5000000000 : ℝ)|^6079 ≤ (22886263397703/50000000000000 : ℝ)^5055
        have hw : |(2610631519/5000000000 : ℝ)|=(2610631519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945386327/10000000000 : ℝ)|^6079 ≤ (1172537493939/20000000000000 : ℝ)^5055
        have hw : |(-945386327/10000000000 : ℝ)|=(945386327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093200739/2000000000 : ℝ)|^6079 ≤ (9672957143021/20000000000000 : ℝ)^5055
        have hw : |(1093200739/2000000000 : ℝ)|=(1093200739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s2_6 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5221263039/10000000000 : ℝ)*x 0 + (1093200739/2000000000 : ℝ)*x 1 + (-945386327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5221263039/10000000000 : ℝ)^6079 ≤ (11443131701487/25000000000000 : ℝ)^5055 := by
    have hnat : (5221263039 : ℕ)^6079*25000000000000^5055 ≤ 11443131701487^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221263039 10000000000 11443131701487 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093200739/2000000000 : ℝ)^6079 ≤ (9672957143021/20000000000000 : ℝ)^5055 := by
    have hnat : (1093200739 : ℕ)^6079*20000000000000^5055 ≤ 9672957143021^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093200739 2000000000 9672957143021 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945386327/10000000000 : ℝ)^6079 ≤ (1172537493939/20000000000000 : ℝ)^5055 := by
    have hnat : (945386327 : ℕ)^6079*20000000000000^5055 ≤ 1172537493939^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945386327 10000000000 1172537493939 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5221263039/10000000000 : ℝ), (1093200739/2000000000 : ℝ), (-945386327/10000000000 : ℝ)] ![(11443131701487/25000000000000 : ℝ), (9672957143021/20000000000000 : ℝ), (1172537493939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5221263039/10000000000 : ℝ)|^6079 ≤ (11443131701487/25000000000000 : ℝ)^5055
        have hw : |(5221263039/10000000000 : ℝ)|=(5221263039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093200739/2000000000 : ℝ)|^6079 ≤ (9672957143021/20000000000000 : ℝ)^5055
        have hw : |(1093200739/2000000000 : ℝ)|=(1093200739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945386327/10000000000 : ℝ)|^6079 ≤ (1172537493939/20000000000000 : ℝ)^5055
        have hw : |(-945386327/10000000000 : ℝ)|=(945386327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_s2_7 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (796901367/2000000000 : ℝ)*x 0 + (4675182887/10000000000 : ℝ)*x 1 + (670198859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796901367/2000000000 : ℝ)^6079 ≤ (6613810783173/20000000000000 : ℝ)^5055 := by
    have hnat : (796901367 : ℕ)^6079*20000000000000^5055 ≤ 6613810783173^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796901367 2000000000 6613810783173 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4675182887/10000000000 : ℝ)^6079 ≤ (20039143128069/50000000000000 : ℝ)^5055 := by
    have hnat : (4675182887 : ℕ)^6079*50000000000000^5055 ≤ 20039143128069^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4675182887 10000000000 20039143128069 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (670198859/2000000000 : ℝ)^6079 ≤ (13426329908361/50000000000000 : ℝ)^5055 := by
    have hnat : (670198859 : ℕ)^6079*50000000000000^5055 ≤ 13426329908361^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670198859 2000000000 13426329908361 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796901367/2000000000 : ℝ), (4675182887/10000000000 : ℝ), (670198859/2000000000 : ℝ)] ![(6613810783173/20000000000000 : ℝ), (20039143128069/50000000000000 : ℝ), (13426329908361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796901367/2000000000 : ℝ)|^6079 ≤ (6613810783173/20000000000000 : ℝ)^5055
        have hw : |(796901367/2000000000 : ℝ)|=(796901367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4675182887/10000000000 : ℝ)|^6079 ≤ (20039143128069/50000000000000 : ℝ)^5055
        have hw : |(4675182887/10000000000 : ℝ)|=(4675182887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(670198859/2000000000 : ℝ)|^6079 ≤ (13426329908361/50000000000000 : ℝ)^5055
        have hw : |(670198859/2000000000 : ℝ)|=(670198859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1769_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17641/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (288/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (9241/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17611/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17641/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (288/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17641/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (288/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17641/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (288/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17641/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (288/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17641/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (288/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17641/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (288/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (288/3125 : ℝ) ^ (6063/1024 : ℝ) ≤ (36993984447711/50000000000000000000 : ℝ) := by
    have hpowers : (288/3125 : ℝ)^6063 ≤ (36993984447711/50000000000000000000 : ℝ)^1024 := by
      have hnat : (288 : ℕ)^6063*50000000000000000000^1024 ≤ 36993984447711^1024*3125^6063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        288 3125 36993984447711 50000000000000000000 6063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (288/3125 : ℝ)) (X := (36993984447711/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17641/100000 : ℝ) ^ (6063/1024 : ℝ) ≤ (1728663237999209/50000000000000000000 : ℝ) := by
    have hpowers : (17641/100000 : ℝ)^6063 ≤ (1728663237999209/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17641 : ℕ)^6063*50000000000000000000^1024 ≤ 1728663237999209^1024*100000^6063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17641 100000 1728663237999209 50000000000000000000 6063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17641/100000 : ℝ)) (X := (1728663237999209/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000036993984447711/25000000000000000000 : ℝ) ≤ (10000002499212719/10000000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (25000036993984447711/25000000000000000000 : ℝ)^1024 ≤ (10000002499212719/10000000000000000 : ℝ)^6063 := by
      have hnat : (25000036993984447711 : ℕ)^1024*10000000000000000^6063 ≤ 10000002499212719^6063*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000036993984447711 25000000000000000000 10000002499212719 10000000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002499212719/10000000000000000 : ℝ)) (X := (25000036993984447711/25000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250044141430561173/1250000000000000000 : ℝ) ≤ (5000029820327633/5000000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (1250044141430561173/1250000000000000000 : ℝ)^1024 ≤ (5000029820327633/5000000000000000 : ℝ)^6063 := by
      have hnat : (1250044141430561173 : ℕ)^1024*5000000000000000^6063 ≤ 5000029820327633^6063*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250044141430561173 1250000000000000000 5000029820327633 5000000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000029820327633/5000000000000000 : ℝ)) (X := (1250044141430561173/1250000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25001728663237999209/25000000000000000000 : ℝ) ≤ (10000116782097813/10000000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (25001728663237999209/25000000000000000000 : ℝ)^1024 ≤ (10000116782097813/10000000000000000 : ℝ)^6063 := by
      have hnat : (25001728663237999209 : ℕ)^1024*10000000000000000^6063 ≤ 10000116782097813^6063*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001728663237999209 25000000000000000000 10000116782097813 10000000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000116782097813/10000000000000000 : ℝ)) (X := (25001728663237999209/25000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(36993984447711/50000000000000000000 : ℝ) ≤ ((84248967824798131271/84250000000000000000 : ℝ)+2*(57141442547/842500000000000 : ℝ)*(288/3125 : ℝ))^(6063/1024 : ℝ) := by
    rw [show (84248967824798131271/84250000000000000000 : ℝ)+2*(57141442547/842500000000000 : ℝ)*(288/3125 : ℝ)=(10000002499212719/10000000000000000 : ℝ) by norm_num, show 1+2*(36993984447711/50000000000000000000 : ℝ)=(25000036993984447711/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1728663237999209/50000000000000000000 : ℝ)+(36993984447711/50000000000000000000 : ℝ) ≤ ((84248967824798131271/84250000000000000000 : ℝ)+(57141442547/842500000000000 : ℝ)*((17641/100000 : ℝ)+(288/3125 : ℝ)))^(6063/1024 : ℝ) := by
    rw [show (84248967824798131271/84250000000000000000 : ℝ)+(57141442547/842500000000000 : ℝ)*((17641/100000 : ℝ)+(288/3125 : ℝ))=(5000029820327633/5000000000000000 : ℝ) by norm_num, show 1+(1728663237999209/50000000000000000000 : ℝ)+(36993984447711/50000000000000000000 : ℝ)=(1250044141430561173/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1728663237999209/50000000000000000000 : ℝ) ≤ ((84248967824798131271/84250000000000000000 : ℝ)+2*(57141442547/842500000000000 : ℝ)*(17641/100000 : ℝ))^(6063/1024 : ℝ) := by
    rw [show (84248967824798131271/84250000000000000000 : ℝ)+2*(57141442547/842500000000000 : ℝ)*(17641/100000 : ℝ)=(10000116782097813/10000000000000000 : ℝ) by norm_num, show 1+2*(1728663237999209/50000000000000000000 : ℝ)=(25001728663237999209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84248967824798131271/84250000000000000000 : ℝ)*(X 1 0+X 2 0)+(57141442547/842500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (288/3125 : ℝ)) (hi := (17641/100000 : ℝ)) (c := (84248967824798131271/84250000000000000000 : ℝ)) (alpha := (57141442547/842500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84248967824798131271/84250000000000000000 : ℝ)*(X 0 1+X 2 1)+(57141442547/842500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (288/3125 : ℝ)) (hi := (17641/100000 : ℝ)) (c := (84248967824798131271/84250000000000000000 : ℝ)) (alpha := (57141442547/842500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84248967824798131271/84250000000000000000 : ℝ)*(X 0 2+X 1 2)+(57141442547/842500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (288/3125 : ℝ)) (hi := (17641/100000 : ℝ)) (c := (84248967824798131271/84250000000000000000 : ℝ)) (alpha := (57141442547/842500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-35123843/312500000 : ℝ)*X 0 0+(5472625889/10000000000 : ℝ)*X 0 1+(2542795403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5323195479/10000000000 : ℝ)*X 1 0+(-662899603/5000000000 : ℝ)*X 1 1+(635698851/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5323195469/10000000000 : ℝ)*X 2 0+(1271397703/2500000000 : ℝ)*X 2 1+(-265159843/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1991695553/5000000000 : ℝ)*X 0 0+(103985719/312500000 : ℝ)*X 0 1+(58726969/125000000 : ℝ)*X 0 2+(1991695553/5000000000 : ℝ)*X 1 0+(103985719/312500000 : ℝ)*X 1 1+(58726969/125000000 : ℝ)*X 1 2+(1991695553/5000000000 : ℝ)*X 2 0+(103985719/312500000 : ℝ)*X 2 1+(58726969/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-281069509/2500000000 : ℝ)*X 0 0+(1018415681/2000000000 : ℝ)*X 0 1+(1093200739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2610631519/5000000000 : ℝ)*X 1 0+(-945386327/10000000000 : ℝ)*X 1 1+(1093200739/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5221263039/10000000000 : ℝ)*X 2 0+(1093200739/2000000000 : ℝ)*X 2 1+(-945386327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((796901367/2000000000 : ℝ)*X 0 0+(4675182887/10000000000 : ℝ)*X 0 1+(670198859/2000000000 : ℝ)*X 0 2+(796901367/2000000000 : ℝ)*X 1 0+(4675182887/10000000000 : ℝ)*X 1 1+(670198859/2000000000 : ℝ)*X 1 2+(796901367/2000000000 : ℝ)*X 2 0+(4675182887/10000000000 : ℝ)*X 2 1+(670198859/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17052331914378744996153149001/2106250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1074569607/100000000000000 : ℝ)*(base19) + (1012426633/100000000000000 : ℝ)*(base23) + (15248079/50000000000000 : ℝ)*(lower2) + (194453167/100000000000000 : ℝ)*(upper3) + (74606187/50000000000000 : ℝ)*(upper5) + (828341961125877/50000000000000 : ℝ)*(major0) + (828341961125877/50000000000000 : ℝ)*(major1) + (828341961125877/50000000000000 : ℝ)*(major2) + (2583753994908873/100000000000000 : ℝ)*(sp0) + (258376170424407/10000000000000 : ℝ)*(sp1) + (645940441596761/25000000000000 : ℝ)*(sp2) + (729602098799487/100000000000000 : ℝ)*(sp3) + (2195976201/25000000000000 : ℝ)*(sp4) + (134851079/5000000000000 : ℝ)*(sp7) + (364802397910533/50000000000000 : ℝ)*(f.failure) + (2583762778813677/100000000000000 : ℝ)*(f.sum) + (48116979862203/10531250000000000000000000000 : ℝ)*base66 + (13333107494339600333/4212500000000000000000000000000000 : ℝ)*base68 + (13230320657597899667/4212500000000000000000000000000000 : ℝ)*base69 + (10080267140877100333/4212500000000000000000000000000000 : ℝ)*base72 + (49109543788281/21062500000000000000000000000 : ℝ)*base74 + (13947196590577100333/4212500000000000000000000000000000 : ℝ)*base76 + (12542659187402100333/4212500000000000000000000000000000 : ℝ)*base78 + (8561491796822899667/4212500000000000000000000000000000 : ℝ)*base79 + (65441433266219/21062500000000000000000000000 : ℝ)*base81 + (69648777/5000000000000000000000 : ℝ)*base90 + (69648777/5000000000000000000000 : ℝ)*base92 + (69648777/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44648877014919747550396734933/4212500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164645463/12500000000000 : ℝ)*(base19) + (703845809/50000000000000 : ℝ)*(base23) + (184405453/50000000000000 : ℝ)*(lower1) + (28548829/12500000000000 : ℝ)*(upper3) + (39953173/100000000000000 : ℝ)*(lower4) + (110144243/50000000000000 : ℝ)*(upper5) + (1714748737802241/100000000000000 : ℝ)*(major0) + (1714748737802241/100000000000000 : ℝ)*(major1) + (1714748737802241/100000000000000 : ℝ)*(major2) + (172820343/25000000000000 : ℝ)*(sp2) + (668580134943937/25000000000000 : ℝ)*(sp4) + (668579805653011/25000000000000 : ℝ)*(sp5) + (1337159220401379/50000000000000 : ℝ)*(sp6) + (37758829126203/5000000000000 : ℝ)*(sp7) + (37758829126203/5000000000000 : ℝ)*(f.failure) + (668580134943937/25000000000000 : ℝ)*(f.sum) + (230910314227327/42125000000000000000000000000 : ℝ)*base65 + (17929944355861321689/8425000000000000000000000000000000 : ℝ)*base68 + (13379517499138678311/8425000000000000000000000000000000 : ℝ)*base69 + (137078793311961321689/8425000000000000000000000000000000 : ℝ)*base72 + (139306988549827/42125000000000000000000000000 : ℝ)*base73 + (122768759408138678311/8425000000000000000000000000000000 : ℝ)*base75 + (35290768703111321689/8425000000000000000000000000000000 : ℝ)*base78 + (1169442574811321689/8425000000000000000000000000000000 : ℝ)*base80 + (48873627373077/42125000000000000000000000000 : ℝ)*base81 + (4310007/500000000000000000000 : ℝ)*base90 + (4310007/500000000000000000000 : ℝ)*base92 + (4310007/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1769_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17641/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (288/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17611/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1769_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1769_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17611/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1769_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1769_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1769_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17611/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1769_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
