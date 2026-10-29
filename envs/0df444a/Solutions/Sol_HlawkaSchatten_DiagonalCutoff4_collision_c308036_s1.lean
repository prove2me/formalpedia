-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308036_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:34:14.06421+00:00
-- url     : https://prove2.me/submissions/ef522733-3193-445a-8330-6fc226ed92c2

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c308036_s1_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1185584193/2000000000 : ℝ)*x 0 + (3374933487/10000000000 : ℝ)*x 1 + (-1703683803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1185584193/2000000000 : ℝ)^35 ≤ (12692706477869/25000000000000 : ℝ)^27 := by
    have hnat : (1185584193 : ℕ)^35*25000000000000^27 ≤ 12692706477869^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185584193 2000000000 12692706477869 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3374933487/10000000000 : ℝ)^35 ≤ (978479972249/4000000000000 : ℝ)^27 := by
    have hnat : (3374933487 : ℕ)^35*4000000000000^27 ≤ 978479972249^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374933487 10000000000 978479972249 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1703683803/5000000000 : ℝ)^35 ≤ (12383587386393/50000000000000 : ℝ)^27 := by
    have hnat : (1703683803 : ℕ)^35*50000000000000^27 ≤ 12383587386393^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703683803 5000000000 12383587386393 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1185584193/2000000000 : ℝ), (3374933487/10000000000 : ℝ), (-1703683803/5000000000 : ℝ)] ![(12692706477869/25000000000000 : ℝ), (978479972249/4000000000000 : ℝ), (12383587386393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1185584193/2000000000 : ℝ)|^35 ≤ (12692706477869/25000000000000 : ℝ)^27
        have hw : |(1185584193/2000000000 : ℝ)|=(1185584193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3374933487/10000000000 : ℝ)|^35 ≤ (978479972249/4000000000000 : ℝ)^27
        have hw : |(3374933487/10000000000 : ℝ)|=(3374933487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1703683803/5000000000 : ℝ)|^35 ≤ (12383587386393/50000000000000 : ℝ)^27
        have hw : |(-1703683803/5000000000 : ℝ)|=(1703683803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5869225563/10000000000 : ℝ)*x 0 + (-1704647273/5000000000 : ℝ)*x 1 + (688411777/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5869225563/10000000000 : ℝ)^35 ≤ (50120125372183/100000000000000 : ℝ)^27 := by
    have hnat : (5869225563 : ℕ)^35*100000000000000^27 ≤ 50120125372183^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5869225563 10000000000 50120125372183 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1704647273/5000000000 : ℝ)^35 ≤ (991413308099/4000000000000 : ℝ)^27 := by
    have hnat : (1704647273 : ℕ)^35*4000000000000^27 ≤ 991413308099^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704647273 5000000000 991413308099 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688411777/2000000000 : ℝ)^35 ≤ (25094541911707/100000000000000 : ℝ)^27 := by
    have hnat : (688411777 : ℕ)^35*100000000000000^27 ≤ 25094541911707^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688411777 2000000000 25094541911707 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5869225563/10000000000 : ℝ), (-1704647273/5000000000 : ℝ), (688411777/2000000000 : ℝ)] ![(50120125372183/100000000000000 : ℝ), (991413308099/4000000000000 : ℝ), (25094541911707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5869225563/10000000000 : ℝ)|^35 ≤ (50120125372183/100000000000000 : ℝ)^27
        have hw : |(5869225563/10000000000 : ℝ)|=(5869225563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1704647273/5000000000 : ℝ)|^35 ≤ (991413308099/4000000000000 : ℝ)^27
        have hw : |(-1704647273/5000000000 : ℝ)|=(1704647273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(688411777/2000000000 : ℝ)|^35 ≤ (25094541911707/100000000000000 : ℝ)^27
        have hw : |(688411777/2000000000 : ℝ)|=(688411777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (109687223/10000000000 : ℝ)*x 0 + (-6459529417/10000000000 : ℝ)*x 1 + (-1302843767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109687223/10000000000 : ℝ)^35 ≤ (144022896017/50000000000000 : ℝ)^27 := by
    have hnat : (109687223 : ℕ)^35*50000000000000^27 ≤ 144022896017^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109687223 10000000000 144022896017 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6459529417/10000000000 : ℝ)^35 ≤ (56749769798861/100000000000000 : ℝ)^27 := by
    have hnat : (6459529417 : ℕ)^35*100000000000000^27 ≤ 56749769798861^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6459529417 10000000000 56749769798861 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302843767/2500000000 : ℝ)^35 ≤ (21481092202559/50000000000000 : ℝ)^27 := by
    have hnat : (1302843767 : ℕ)^35*50000000000000^27 ≤ 21481092202559^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302843767 2500000000 21481092202559 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109687223/10000000000 : ℝ), (-6459529417/10000000000 : ℝ), (-1302843767/2500000000 : ℝ)] ![(144022896017/50000000000000 : ℝ), (56749769798861/100000000000000 : ℝ), (21481092202559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109687223/10000000000 : ℝ)|^35 ≤ (144022896017/50000000000000 : ℝ)^27
        have hw : |(109687223/10000000000 : ℝ)|=(109687223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6459529417/10000000000 : ℝ)|^35 ≤ (56749769798861/100000000000000 : ℝ)^27
        have hw : |(-6459529417/10000000000 : ℝ)|=(6459529417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1302843767/2500000000 : ℝ)|^35 ≤ (21481092202559/50000000000000 : ℝ)^27
        have hw : |(-1302843767/2500000000 : ℝ)|=(1302843767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (13000367/25000000 : ℝ)*x 0 + (1179806679/2500000000 : ℝ)*x 1 + (-563986631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13000367/25000000 : ℝ)^35 ≤ (21421115530901/50000000000000 : ℝ)^27 := by
    have hnat : (13000367 : ℕ)^35*50000000000000^27 ≤ 21421115530901^27*25000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13000367 25000000 21421115530901 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1179806679/2500000000 : ℝ)^35 ≤ (3777808853371/10000000000000 : ℝ)^27 := by
    have hnat : (1179806679 : ℕ)^35*10000000000000^27 ≤ 3777808853371^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179806679 2500000000 3777808853371 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563986631/2000000000 : ℝ)^35 ≤ (19379680390037/100000000000000 : ℝ)^27 := by
    have hnat : (563986631 : ℕ)^35*100000000000000^27 ≤ 19379680390037^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563986631 2000000000 19379680390037 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13000367/25000000 : ℝ), (1179806679/2500000000 : ℝ), (-563986631/2000000000 : ℝ)] ![(21421115530901/50000000000000 : ℝ), (3777808853371/10000000000000 : ℝ), (19379680390037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13000367/25000000 : ℝ)|^35 ≤ (21421115530901/50000000000000 : ℝ)^27
        have hw : |(13000367/25000000 : ℝ)|=(13000367/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1179806679/2500000000 : ℝ)|^35 ≤ (3777808853371/10000000000000 : ℝ)^27
        have hw : |(1179806679/2500000000 : ℝ)|=(1179806679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563986631/2000000000 : ℝ)|^35 ≤ (19379680390037/100000000000000 : ℝ)^27
        have hw : |(-563986631/2000000000 : ℝ)|=(563986631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5924050161/10000000000 : ℝ)*x 0 + (-966323711/5000000000 : ℝ)*x 1 + (36581649/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5924050161/10000000000 : ℝ)^35 ≤ (12681963732731/25000000000000 : ℝ)^27 := by
    have hnat : (5924050161 : ℕ)^35*25000000000000^27 ≤ 12681963732731^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5924050161 10000000000 12681963732731 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966323711/5000000000 : ℝ)^35 ≤ (5937618699813/50000000000000 : ℝ)^27 := by
    have hnat : (966323711 : ℕ)^35*50000000000000^27 ≤ 5937618699813^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966323711 5000000000 5937618699813 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36581649/78125000 : ℝ)^35 ≤ (37396907650977/100000000000000 : ℝ)^27 := by
    have hnat : (36581649 : ℕ)^35*100000000000000^27 ≤ 37396907650977^27*78125000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36581649 78125000 37396907650977 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5924050161/10000000000 : ℝ), (-966323711/5000000000 : ℝ), (36581649/78125000 : ℝ)] ![(12681963732731/25000000000000 : ℝ), (5937618699813/50000000000000 : ℝ), (37396907650977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5924050161/10000000000 : ℝ)|^35 ≤ (12681963732731/25000000000000 : ℝ)^27
        have hw : |(5924050161/10000000000 : ℝ)|=(5924050161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-966323711/5000000000 : ℝ)|^35 ≤ (5937618699813/50000000000000 : ℝ)^27
        have hw : |(-966323711/5000000000 : ℝ)|=(966323711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36581649/78125000 : ℝ)|^35 ≤ (37396907650977/100000000000000 : ℝ)^27
        have hw : |(36581649/78125000 : ℝ)|=(36581649/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5216665157/10000000000 : ℝ)*x 0 + (-336546499/1000000000 : ℝ)*x 1 + (-4212757139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5216665157/10000000000 : ℝ)^35 ≤ (43018725807251/100000000000000 : ℝ)^27 := by
    have hnat : (5216665157 : ℕ)^35*100000000000000^27 ≤ 43018725807251^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216665157 10000000000 43018725807251 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336546499/1000000000 : ℝ)^35 ≤ (12186536383311/50000000000000 : ℝ)^27 := by
    have hnat : (336546499 : ℕ)^35*50000000000000^27 ≤ 12186536383311^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336546499 1000000000 12186536383311 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4212757139/10000000000 : ℝ)^35 ≤ (32608201417593/100000000000000 : ℝ)^27 := by
    have hnat : (4212757139 : ℕ)^35*100000000000000^27 ≤ 32608201417593^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212757139 10000000000 32608201417593 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5216665157/10000000000 : ℝ), (-336546499/1000000000 : ℝ), (-4212757139/10000000000 : ℝ)] ![(43018725807251/100000000000000 : ℝ), (12186536383311/50000000000000 : ℝ), (32608201417593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5216665157/10000000000 : ℝ)|^35 ≤ (43018725807251/100000000000000 : ℝ)^27
        have hw : |(5216665157/10000000000 : ℝ)|=(5216665157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336546499/1000000000 : ℝ)|^35 ≤ (12186536383311/50000000000000 : ℝ)^27
        have hw : |(-336546499/1000000000 : ℝ)|=(336546499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4212757139/10000000000 : ℝ)|^35 ≤ (32608201417593/100000000000000 : ℝ)^27
        have hw : |(-4212757139/10000000000 : ℝ)|=(4212757139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (19779023/2500000000 : ℝ)*x 0 + (-1006895933/2000000000 : ℝ)*x 1 + (-6632728897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19779023/2500000000 : ℝ)^35 ≤ (2357428297/1250000000000 : ℝ)^27 := by
    have hnat : (19779023 : ℕ)^35*1250000000000^27 ≤ 2357428297^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19779023 2500000000 2357428297 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006895933/2000000000 : ℝ)^35 ≤ (41081362621087/100000000000000 : ℝ)^27 := by
    have hnat : (1006895933 : ℕ)^35*100000000000000^27 ≤ 41081362621087^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006895933 2000000000 41081362621087 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6632728897/10000000000 : ℝ)^35 ≤ (58730043099989/100000000000000 : ℝ)^27 := by
    have hnat : (6632728897 : ℕ)^35*100000000000000^27 ≤ 58730043099989^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6632728897 10000000000 58730043099989 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19779023/2500000000 : ℝ), (-1006895933/2000000000 : ℝ), (-6632728897/10000000000 : ℝ)] ![(2357428297/1250000000000 : ℝ), (41081362621087/100000000000000 : ℝ), (58730043099989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19779023/2500000000 : ℝ)|^35 ≤ (2357428297/1250000000000 : ℝ)^27
        have hw : |(19779023/2500000000 : ℝ)|=(19779023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1006895933/2000000000 : ℝ)|^35 ≤ (41081362621087/100000000000000 : ℝ)^27
        have hw : |(-1006895933/2000000000 : ℝ)|=(1006895933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6632728897/10000000000 : ℝ)|^35 ≤ (58730043099989/100000000000000 : ℝ)^27
        have hw : |(-6632728897/10000000000 : ℝ)|=(6632728897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4124701461/10000000000 : ℝ)*x 0 + (714924991/2000000000 : ℝ)*x 1 + (-5113401113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4124701461/10000000000 : ℝ)^35 ≤ (31727419349517/100000000000000 : ℝ)^27 := by
    have hnat : (4124701461 : ℕ)^35*100000000000000^27 ≤ 31727419349517^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124701461 10000000000 31727419349517 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (714924991/2000000000 : ℝ)^35 ≤ (13177236302249/50000000000000 : ℝ)^27 := by
    have hnat : (714924991 : ℕ)^35*50000000000000^27 ≤ 13177236302249^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714924991 2000000000 13177236302249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5113401113/10000000000 : ℝ)^35 ≤ (41918108021703/100000000000000 : ℝ)^27 := by
    have hnat : (5113401113 : ℕ)^35*100000000000000^27 ≤ 41918108021703^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113401113 10000000000 41918108021703 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4124701461/10000000000 : ℝ), (714924991/2000000000 : ℝ), (-5113401113/10000000000 : ℝ)] ![(31727419349517/100000000000000 : ℝ), (13177236302249/50000000000000 : ℝ), (41918108021703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4124701461/10000000000 : ℝ)|^35 ≤ (31727419349517/100000000000000 : ℝ)^27
        have hw : |(4124701461/10000000000 : ℝ)|=(4124701461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(714924991/2000000000 : ℝ)|^35 ≤ (13177236302249/50000000000000 : ℝ)^27
        have hw : |(714924991/2000000000 : ℝ)|=(714924991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5113401113/10000000000 : ℝ)|^35 ≤ (41918108021703/100000000000000 : ℝ)^27
        have hw : |(-5113401113/10000000000 : ℝ)|=(5113401113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7592653763/10000000000 : ℝ)*x 0 + (-94833537/500000000 : ℝ)*x 1 + (84785453/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7592653763/10000000000 : ℝ)^35 ≤ (69976893886723/100000000000000 : ℝ)^27 := by
    have hnat : (7592653763 : ℕ)^35*100000000000000^27 ≤ 69976893886723^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7592653763 10000000000 69976893886723 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94833537/500000000 : ℝ)^35 ≤ (11589471493767/100000000000000 : ℝ)^27 := by
    have hnat : (94833537 : ℕ)^35*100000000000000^27 ≤ 11589471493767^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94833537 500000000 11589471493767 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84785453/312500000 : ℝ)^35 ≤ (1843363460389/10000000000000 : ℝ)^27 := by
    have hnat : (84785453 : ℕ)^35*10000000000000^27 ≤ 1843363460389^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84785453 312500000 1843363460389 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7592653763/10000000000 : ℝ), (-94833537/500000000 : ℝ), (84785453/312500000 : ℝ)] ![(69976893886723/100000000000000 : ℝ), (11589471493767/100000000000000 : ℝ), (1843363460389/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7592653763/10000000000 : ℝ)|^35 ≤ (69976893886723/100000000000000 : ℝ)^27
        have hw : |(7592653763/10000000000 : ℝ)|=(7592653763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-94833537/500000000 : ℝ)|^35 ≤ (11589471493767/100000000000000 : ℝ)^27
        have hw : |(-94833537/500000000 : ℝ)|=(94833537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84785453/312500000 : ℝ)|^35 ≤ (1843363460389/10000000000000 : ℝ)^27
        have hw : |(84785453/312500000 : ℝ)|=(84785453/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6719472877/10000000000 : ℝ)*x 0 + (-499928969/2000000000 : ℝ)*x 1 + (-658636749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6719472877/10000000000 : ℝ)^35 ≤ (59727627778453/100000000000000 : ℝ)^27 := by
    have hnat : (6719472877 : ℕ)^35*100000000000000^27 ≤ 59727627778453^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6719472877 10000000000 59727627778453 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499928969/2000000000 : ℝ)^35 ≤ (16575700084667/100000000000000 : ℝ)^27 := by
    have hnat : (499928969 : ℕ)^35*100000000000000^27 ≤ 16575700084667^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499928969 2000000000 16575700084667 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658636749/2000000000 : ℝ)^35 ≤ (23696672125727/100000000000000 : ℝ)^27 := by
    have hnat : (658636749 : ℕ)^35*100000000000000^27 ≤ 23696672125727^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658636749 2000000000 23696672125727 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6719472877/10000000000 : ℝ), (-499928969/2000000000 : ℝ), (-658636749/2000000000 : ℝ)] ![(59727627778453/100000000000000 : ℝ), (16575700084667/100000000000000 : ℝ), (23696672125727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6719472877/10000000000 : ℝ)|^35 ≤ (59727627778453/100000000000000 : ℝ)^27
        have hw : |(6719472877/10000000000 : ℝ)|=(6719472877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499928969/2000000000 : ℝ)|^35 ≤ (16575700084667/100000000000000 : ℝ)^27
        have hw : |(-499928969/2000000000 : ℝ)|=(499928969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658636749/2000000000 : ℝ)|^35 ≤ (23696672125727/100000000000000 : ℝ)^27
        have hw : |(-658636749/2000000000 : ℝ)|=(658636749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (79158681/10000000000 : ℝ)*x 0 + (-266659357/400000000 : ℝ)*x 1 + (-4997771659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79158681/10000000000 : ℝ)^35 ≤ (23590734641/12500000000000 : ℝ)^27 := by
    have hnat : (79158681 : ℕ)^35*12500000000000^27 ≤ 23590734641^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79158681 10000000000 23590734641 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266659357/400000000 : ℝ)^35 ≤ (59117780549239/100000000000000 : ℝ)^27 := by
    have hnat : (266659357 : ℕ)^35*100000000000000^27 ≤ 59117780549239^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266659357 400000000 59117780549239 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4997771659/10000000000 : ℝ)^35 ≤ (40693493558009/100000000000000 : ℝ)^27 := by
    have hnat : (4997771659 : ℕ)^35*100000000000000^27 ≤ 40693493558009^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997771659 10000000000 40693493558009 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(79158681/10000000000 : ℝ), (-266659357/400000000 : ℝ), (-4997771659/10000000000 : ℝ)] ![(23590734641/12500000000000 : ℝ), (59117780549239/100000000000000 : ℝ), (40693493558009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(79158681/10000000000 : ℝ)|^35 ≤ (23590734641/12500000000000 : ℝ)^27
        have hw : |(79158681/10000000000 : ℝ)|=(79158681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266659357/400000000 : ℝ)|^35 ≤ (59117780549239/100000000000000 : ℝ)^27
        have hw : |(-266659357/400000000 : ℝ)|=(266659357/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4997771659/10000000000 : ℝ)|^35 ≤ (40693493558009/100000000000000 : ℝ)^27
        have hw : |(-4997771659/10000000000 : ℝ)|=(4997771659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1534060921/2000000000 : ℝ)*x 0 + (2631038141/10000000000 : ℝ)*x 1 + (-467547201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1534060921/2000000000 : ℝ)^35 ≤ (70906004580231/100000000000000 : ℝ)^27 := by
    have hnat : (1534060921 : ℕ)^35*100000000000000^27 ≤ 70906004580231^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534060921 2000000000 70906004580231 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631038141/10000000000 : ℝ)^35 ≤ (4428462515811/25000000000000 : ℝ)^27 := by
    have hnat : (2631038141 : ℕ)^35*25000000000000^27 ≤ 4428462515811^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631038141 10000000000 4428462515811 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467547201/2500000000 : ℝ)^35 ≤ (71125908453/625000000000 : ℝ)^27 := by
    have hnat : (467547201 : ℕ)^35*625000000000^27 ≤ 71125908453^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467547201 2500000000 71125908453 625000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1534060921/2000000000 : ℝ), (2631038141/10000000000 : ℝ), (-467547201/2500000000 : ℝ)] ![(70906004580231/100000000000000 : ℝ), (4428462515811/25000000000000 : ℝ), (71125908453/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1534060921/2000000000 : ℝ)|^35 ≤ (70906004580231/100000000000000 : ℝ)^27
        have hw : |(1534060921/2000000000 : ℝ)|=(1534060921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631038141/10000000000 : ℝ)|^35 ≤ (4428462515811/25000000000000 : ℝ)^27
        have hw : |(2631038141/10000000000 : ℝ)|=(2631038141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467547201/2500000000 : ℝ)|^35 ≤ (71125908453/625000000000 : ℝ)^27
        have hw : |(-467547201/2500000000 : ℝ)|=(467547201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1011734777/2500000000 : ℝ)*x 0 + (-512472279/1000000000 : ℝ)*x 1 + (1821372149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011734777/2500000000 : ℝ)^35 ≤ (7738553081051/25000000000000 : ℝ)^27 := by
    have hnat : (1011734777 : ℕ)^35*25000000000000^27 ≤ 7738553081051^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011734777 2500000000 7738553081051 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512472279/1000000000 : ℝ)^35 ≤ (105096147213/250000000000 : ℝ)^27 := by
    have hnat : (512472279 : ℕ)^35*250000000000^27 ≤ 105096147213^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512472279 1000000000 105096147213 250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1821372149/5000000000 : ℝ)^35 ≤ (3375916096947/12500000000000 : ℝ)^27 := by
    have hnat : (1821372149 : ℕ)^35*12500000000000^27 ≤ 3375916096947^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821372149 5000000000 3375916096947 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1011734777/2500000000 : ℝ), (-512472279/1000000000 : ℝ), (1821372149/5000000000 : ℝ)] ![(7738553081051/25000000000000 : ℝ), (105096147213/250000000000 : ℝ), (3375916096947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1011734777/2500000000 : ℝ)|^35 ≤ (7738553081051/25000000000000 : ℝ)^27
        have hw : |(1011734777/2500000000 : ℝ)|=(1011734777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512472279/1000000000 : ℝ)|^35 ≤ (105096147213/250000000000 : ℝ)^27
        have hw : |(-512472279/1000000000 : ℝ)|=(512472279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1821372149/5000000000 : ℝ)|^35 ≤ (3375916096947/12500000000000 : ℝ)^27
        have hw : |(1821372149/5000000000 : ℝ)|=(1821372149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308036_s1_s1_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6717573967/10000000000 : ℝ)*x 0 + (-827833443/2500000000 : ℝ)*x 1 + (-62061539/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6717573967/10000000000 : ℝ)^35 ≤ (14926437155943/25000000000000 : ℝ)^27 := by
    have hnat : (6717573967 : ℕ)^35*25000000000000^27 ≤ 14926437155943^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6717573967 10000000000 14926437155943 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827833443/2500000000 : ℝ)^35 ≤ (11933054309197/50000000000000 : ℝ)^27 := by
    have hnat : (827833443 : ℕ)^35*50000000000000^27 ≤ 11933054309197^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827833443 2500000000 11933054309197 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62061539/250000000 : ℝ)^35 ≤ (16428142746111/100000000000000 : ℝ)^27 := by
    have hnat : (62061539 : ℕ)^35*100000000000000^27 ≤ 16428142746111^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62061539 250000000 16428142746111 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6717573967/10000000000 : ℝ), (-827833443/2500000000 : ℝ), (-62061539/250000000 : ℝ)] ![(14926437155943/25000000000000 : ℝ), (11933054309197/50000000000000 : ℝ), (16428142746111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6717573967/10000000000 : ℝ)|^35 ≤ (14926437155943/25000000000000 : ℝ)^27
        have hw : |(6717573967/10000000000 : ℝ)|=(6717573967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-827833443/2500000000 : ℝ)|^35 ≤ (11933054309197/50000000000000 : ℝ)^27
        have hw : |(-827833443/2500000000 : ℝ)|=(827833443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62061539/250000000 : ℝ)|^35 ≤ (16428142746111/100000000000000 : ℝ)^27
        have hw : |(-62061539/250000000 : ℝ)|=(62061539/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308036_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((3719/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3719/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2619/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2619/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21707/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-21707/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3483/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3483/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-64629/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8131/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8131/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (3719/6250 : ℝ) ^ (17/4 : ℝ) ≤ (2202171713877941991/20000000000000000000 : ℝ) := by
    have hpowers : (3719/6250 : ℝ)^17 ≤ (2202171713877941991/20000000000000000000 : ℝ)^4 := by
      have hnat : (3719 : ℕ)^17*20000000000000000000^4 ≤ 2202171713877941991^4*6250^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3719 6250 2202171713877941991 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3719/6250 : ℝ)) (X := (2202171713877941991/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (22202171713877941991/20000000000000000000 : ℝ) ≤ (10248828508785329/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (22202171713877941991/20000000000000000000 : ℝ)^4 ≤ (10248828508785329/10000000000000000 : ℝ)^17 := by
      have hnat : (22202171713877941991 : ℕ)^4*10000000000000000^17 ≤ 10248828508785329^17*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22202171713877941991 20000000000000000000 10248828508785329 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10248828508785329/10000000000000000 : ℝ)) (X := (22202171713877941991/20000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12202171713877941991/10000000000000000000 : ℝ) ≤ (10479441769106961/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (12202171713877941991/10000000000000000000 : ℝ)^4 ≤ (10479441769106961/10000000000000000 : ℝ)^17 := by
      have hnat : (12202171713877941991 : ℕ)^4*10000000000000000^17 ≤ 10479441769106961^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12202171713877941991 10000000000000000000 10479441769106961 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10479441769106961/10000000000000000 : ℝ)) (X := (12202171713877941991/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(248828508785329/5950400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(7206664385051/185950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (3719/6250 : ℝ)) (alpha := (248828508785329/5950400000000000 : ℝ)) (beta := (7206664385051/185950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3719/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(248828508785329/5950400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(7206664385051/185950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2619/3125 : ℝ) ^ (17/4 : ℝ) ≤ (5900289067726510603/12500000000000000000 : ℝ) := by
    have hpowers : (2619/3125 : ℝ)^17 ≤ (5900289067726510603/12500000000000000000 : ℝ)^4 := by
      have hnat : (2619 : ℕ)^17*12500000000000000000^4 ≤ 5900289067726510603^4*3125^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2619 3125 5900289067726510603 12500000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2619/3125 : ℝ)) (X := (5900289067726510603/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (18400289067726510603/12500000000000000000 : ℝ) ≤ (1369050090748223/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (18400289067726510603/12500000000000000000 : ℝ)^4 ≤ (1369050090748223/1250000000000000 : ℝ)^17 := by
      have hnat : (18400289067726510603 : ℕ)^4*1250000000000000^17 ≤ 1369050090748223^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18400289067726510603 12500000000000000000 1369050090748223 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1369050090748223/1250000000000000 : ℝ)) (X := (18400289067726510603/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12150289067726510603/6250000000000000000 : ℝ) ≤ (11693134981717391/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (12150289067726510603/6250000000000000000 : ℝ)^4 ≤ (11693134981717391/10000000000000000 : ℝ)^17 := by
      have hnat : (12150289067726510603 : ℕ)^4*10000000000000000^17 ≤ 11693134981717391^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12150289067726510603 6250000000000000000 11693134981717391 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11693134981717391/10000000000000000 : ℝ)) (X := (12150289067726510603/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(39683363582741/349200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(740734255731607/8380800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (2619/3125 : ℝ)) (alpha := (39683363582741/349200000000000 : ℝ)) (beta := (740734255731607/8380800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2619/3125 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(39683363582741/349200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(740734255731607/8380800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (21707/25000 : ℝ) ^ (17/4 : ℝ) ≤ (13716526547672145621/25000000000000000000 : ℝ) := by
    have hpowers : (21707/25000 : ℝ)^17 ≤ (13716526547672145621/25000000000000000000 : ℝ)^4 := by
      have hnat : (21707 : ℕ)^17*25000000000000000000^4 ≤ 13716526547672145621^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21707 25000 13716526547672145621 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21707/25000 : ℝ)) (X := (13716526547672145621/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (38716526547672145621/25000000000000000000 : ℝ) ≤ (11083977068030717/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (38716526547672145621/25000000000000000000 : ℝ)^4 ≤ (11083977068030717/10000000000000000 : ℝ)^17 := by
      have hnat : (38716526547672145621 : ℕ)^4*10000000000000000^17 ≤ 11083977068030717^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38716526547672145621 25000000000000000000 11083977068030717 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11083977068030717/10000000000000000 : ℝ)) (X := (38716526547672145621/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26216526547672145621/12500000000000000000 : ℝ) ≤ (743988002475169/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (26216526547672145621/12500000000000000000 : ℝ)^4 ≤ (743988002475169/625000000000000 : ℝ)^17 := by
      have hnat : (26216526547672145621 : ℕ)^4*625000000000000^17 ≤ 743988002475169^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26216526547672145621 12500000000000000000 743988002475169 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (743988002475169/625000000000000 : ℝ)) (X := (26216526547672145621/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(154853866861531/1240400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(819830971571987/8682800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (21707/25000 : ℝ)) (alpha := (154853866861531/1240400000000000 : ℝ)) (beta := (819830971571987/8682800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (21707/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(154853866861531/1240400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(819830971571987/8682800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((1185584193/2000000000 : ℝ)*X 1 0+(3374933487/10000000000 : ℝ)*X 1 1+(-1703683803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5869225563/10000000000 : ℝ)*X 2 0+(-1704647273/5000000000 : ℝ)*X 2 1+(688411777/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((109687223/10000000000 : ℝ)*X 0 0+(-6459529417/10000000000 : ℝ)*X 0 1+(-1302843767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((13000367/25000000 : ℝ)*X 1 0+(1179806679/2500000000 : ℝ)*X 1 1+(-563986631/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5924050161/10000000000 : ℝ)*X 2 0+(-966323711/5000000000 : ℝ)*X 2 1+(36581649/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5216665157/10000000000 : ℝ)*X 0 0+(-336546499/1000000000 : ℝ)*X 0 1+(-4212757139/10000000000 : ℝ)*X 0 2+(5216665157/10000000000 : ℝ)*X 1 0+(-336546499/1000000000 : ℝ)*X 1 1+(-4212757139/10000000000 : ℝ)*X 1 2+(5216665157/10000000000 : ℝ)*X 2 0+(-336546499/1000000000 : ℝ)*X 2 1+(-4212757139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((19779023/2500000000 : ℝ)*X 0 0+(-1006895933/2000000000 : ℝ)*X 0 1+(-6632728897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4124701461/10000000000 : ℝ)*X 1 0+(714924991/2000000000 : ℝ)*X 1 1+(-5113401113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7592653763/10000000000 : ℝ)*X 2 0+(-94833537/500000000 : ℝ)*X 2 1+(84785453/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((6719472877/10000000000 : ℝ)*X 0 0+(-499928969/2000000000 : ℝ)*X 0 1+(-658636749/2000000000 : ℝ)*X 0 2+(6719472877/10000000000 : ℝ)*X 1 0+(-499928969/2000000000 : ℝ)*X 1 1+(-658636749/2000000000 : ℝ)*X 1 2+(6719472877/10000000000 : ℝ)*X 2 0+(-499928969/2000000000 : ℝ)*X 2 1+(-658636749/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((79158681/10000000000 : ℝ)*X 0 0+(-266659357/400000000 : ℝ)*X 0 1+(-4997771659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1534060921/2000000000 : ℝ)*X 1 0+(2631038141/10000000000 : ℝ)*X 1 1+(-467547201/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1011734777/2500000000 : ℝ)*X 2 0+(-512472279/1000000000 : ℝ)*X 2 1+(1821372149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((6717573967/10000000000 : ℝ)*X 0 0+(-827833443/2500000000 : ℝ)*X 0 1+(-62061539/250000000 : ℝ)*X 0 2+(6717573967/10000000000 : ℝ)*X 1 0+(-827833443/2500000000 : ℝ)*X 1 1+(-62061539/250000000 : ℝ)*X 1 2+(6717573967/10000000000 : ℝ)*X 2 0+(-827833443/2500000000 : ℝ)*X 2 1+(-62061539/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308036_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((3483/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3483/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (356356314558101606272513/45119550000000000000000000000 : ℝ) := by norm_num
    linear_combination (1673802611/1000000000000 : ℝ)*(base7) + (160493859029/250000000000 : ℝ)*(base39) + (45726117231/200000000000 : ℝ)*(base50) + (135481/62500000000 : ℝ)*(base60) + (2083145768203/1000000000000 : ℝ)*(major_s1_0) + (2083145768203/1000000000000 : ℝ)*(major_s1_1) + (2083145768203/1000000000000 : ℝ)*(major_s1_2) + (828223/500000000000 : ℝ)*(sp_s1_2) + (2835969436753/1000000000000 : ℝ)*(sp_s1_7) + (354491617561/125000000000 : ℝ)*(sp_s1_8) + (2835936981747/1000000000000 : ℝ)*(sp_s1_9) + (1330965153061/1000000000000 : ℝ)*(sp_s1_13) + (7299253/200000000000 : ℝ)*(sp_s1_15) + (192491/6250000000 : ℝ)*(sp_s1_22) + (26585827009/20000000000 : ℝ)*(f.failure) + (2835969436753/1000000000000 : ℝ)*(f.sum) + (76895080275502577/270717300000000000000000000000 : ℝ)*base62 + (7266691668528119/8682800000000000000000000000 : ℝ)*base65 + (846120959796419/8380800000000000000000000000 : ℝ)*base67 + (464909572994887/1240400000000000000000000000 : ℝ)*base68 + (4205710478105214867/129165332800000000000000000000000 : ℝ)*base70 + (64927761148433/185950000000000000000000000 : ℝ)*base73 + (363616835751817/349200000000000000000000000 : ℝ)*base74 + (2679422499055387/5950400000000000000000000000 : ℝ)*base77 + (25086322426176303851/31168195200000000000000000000000 : ℝ)*base78 + (1399/2000000000000000 : ℝ)*base87 + (1399/2000000000000000 : ℝ)*base89 + (1399/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-64629/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9843898225839646651936899271/767083915200000000000000000000000 : ℝ) := by norm_num
    linear_combination (386489785361/500000000000 : ℝ)*(base7) + (672256296859/1000000000000 : ℝ)*(base39) + (27611081371/50000000000 : ℝ)*(base40) + (2688943/500000000000 : ℝ)*(base53) + (13487/12500000000 : ℝ)*(base60) + (2408850815367/1000000000000 : ℝ)*(major_s1_0) + (2408850815367/1000000000000 : ℝ)*(major_s1_1) + (2408845437481/1000000000000 : ℝ)*(major_s1_2) + (54685907/1000000000000 : ℝ)*(sp_s1_1) + (2408411/125000000000 : ℝ)*(sp_s1_9) + (2805767628371/1000000000000 : ℝ)*(sp_s1_14) + (21919632363/7812500000 : ℝ)*(sp_s1_15) + (2805753738969/1000000000000 : ℝ)*(sp_s1_16) + (18047726141/7812500000 : ℝ)*(sp_s1_19) + (768564687663/500000000000 : ℝ)*(f.failure) + (2805773006257/1000000000000 : ℝ)*(f.sum) + (3067236592370111/5156520000000000000000000000 : ℝ)*base62 + (23569134392403/177200000000000000000000000 : ℝ)*base64 + (306919376434997/2793600000000000000000000000 : ℝ)*base67 + (148147466283827/177200000000000000000000000 : ℝ)*base68 + (520090651229927559/2636027200000000000000000000000 : ℝ)*base70 + (17370585986947/185950000000000000000000000 : ℝ)*base73 + (31421015166391/116400000000000000000000000 : ℝ)*base74 + (3199548446016983/5950400000000000000000000000 : ℝ)*base77 + (1169722046572313587/10389398400000000000000000000000 : ℝ)*base79 + (6393/50000000000000000 : ℝ)*base87 + (6393/50000000000000000 : ℝ)*base89 + (6393/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8131/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8131/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2184840384168622356796510283/671198425800000000000000000000000 : ℝ) := by norm_num
    linear_combination (153572624757/200000000000 : ℝ)*(base7) + (171065811109/250000000000 : ℝ)*(base39) + (21261073253/200000000000 : ℝ)*(base40) + (134613/250000000000 : ℝ)*(base43) + (93461/125000000000 : ℝ)*(base50) + (151747166637/62500000000 : ℝ)*(major_s1_0) + (2427954127739/1000000000000 : ℝ)*(major_s1_1) + (151747166637/62500000000 : ℝ)*(major_s1_2) + (22215931/1000000000000 : ℝ)*(sp_s1_2) + (1694717/200000000000 : ℝ)*(sp_s1_8) + (2834935590717/1000000000000 : ℝ)*(sp_s1_20) + (88591489237/31250000000 : ℝ)*(sp_s1_21) + (1417456687393/500000000000 : ℝ)*(sp_s1_22) + (1158591498397/500000000000 : ℝ)*(sp_s1_25) + (1549319873009/1000000000000 : ℝ)*(f.failure) + (2834936129169/1000000000000 : ℝ)*(f.sum) + (84598640129741719/216573840000000000000000000000 : ℝ)*base63 + (663338881836817/1085350000000000000000000000 : ℝ)*base65 + (1178296352338867/8380800000000000000000000000 : ℝ)*base67 + (9427907316613/19381250000000000000000000 : ℝ)*base69 + (57186664581689613/8072833300000000000000000000000 : ℝ)*base70 + (175932367929863/185950000000000000000000000 : ℝ)*base72 + (144899275334719/349200000000000000000000000 : ℝ)*base75 + (266398417851033/371900000000000000000000000 : ℝ)*base77 + (671152599355424083/1246727808000000000000000000000 : ℝ)*base78 + (86601/100000000000000000 : ℝ)*base86 + (13399/100000000000000000 : ℝ)*base89 + (86601/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((3719/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3719/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2619/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2619/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21707/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-21707/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3483/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3483/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64629/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-64629/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8131/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8131/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308036_s1 p hpa hpb X hX hprev0

#print axioms solution
