-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308051_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:36:10.095034+00:00
-- url     : https://prove2.me/submissions/197173f8-bde1-4f99-99ce-8e3c17ca1567

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
theorem collision_support_c308051_s2_s2_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-770665641/2000000000 : ℝ)*x 0 + (3852197669/10000000000 : ℝ)*x 1 + (102261127/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (770665641/2000000000 : ℝ)^35 ≤ (14524150714239/50000000000000 : ℝ)^27 := by
    have hnat : (770665641 : ℕ)^35*50000000000000^27 ≤ 14524150714239^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770665641 2000000000 14524150714239 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3852197669/10000000000 : ℝ)^35 ≤ (29037254169401/100000000000000 : ℝ)^27 := by
    have hnat : (3852197669 : ℕ)^35*100000000000000^27 ≤ 29037254169401^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3852197669 10000000000 29037254169401 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102261127/200000000 : ℝ)^35 ≤ (2619652774061/6250000000000 : ℝ)^27 := by
    have hnat : (102261127 : ℕ)^35*6250000000000^27 ≤ 2619652774061^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102261127 200000000 2619652774061 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-770665641/2000000000 : ℝ), (3852197669/10000000000 : ℝ), (102261127/200000000 : ℝ)] ![(14524150714239/50000000000000 : ℝ), (29037254169401/100000000000000 : ℝ), (2619652774061/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-770665641/2000000000 : ℝ)|^35 ≤ (14524150714239/50000000000000 : ℝ)^27
        have hw : |(-770665641/2000000000 : ℝ)|=(770665641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3852197669/10000000000 : ℝ)|^35 ≤ (29037254169401/100000000000000 : ℝ)^27
        have hw : |(3852197669/10000000000 : ℝ)|=(3852197669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102261127/200000000 : ℝ)|^35 ≤ (2619652774061/6250000000000 : ℝ)^27
        have hw : |(102261127/200000000 : ℝ)|=(102261127/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7824071/25000000 : ℝ)*x 0 + (-195544387/625000000 : ℝ)*x 1 + (63621787/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7824071/25000000 : ℝ)^35 ≤ (11091215816543/50000000000000 : ℝ)^27 := by
    have hnat : (7824071 : ℕ)^35*50000000000000^27 ≤ 11091215816543^27*25000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7824071 25000000 11091215816543 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195544387/625000000 : ℝ)^35 ≤ (2217399551109/10000000000000 : ℝ)^27 := by
    have hnat : (195544387 : ℕ)^35*10000000000000^27 ≤ 2217399551109^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195544387 625000000 2217399551109 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63621787/100000000 : ℝ)^35 ≤ (55643572845309/100000000000000 : ℝ)^27 := by
    have hnat : (63621787 : ℕ)^35*100000000000000^27 ≤ 55643572845309^27*100000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63621787 100000000 55643572845309 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7824071/25000000 : ℝ), (-195544387/625000000 : ℝ), (63621787/100000000 : ℝ)] ![(11091215816543/50000000000000 : ℝ), (2217399551109/10000000000000 : ℝ), (55643572845309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7824071/25000000 : ℝ)|^35 ≤ (11091215816543/50000000000000 : ℝ)^27
        have hw : |(7824071/25000000 : ℝ)|=(7824071/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195544387/625000000 : ℝ)|^35 ≤ (2217399551109/10000000000000 : ℝ)^27
        have hw : |(-195544387/625000000 : ℝ)|=(195544387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63621787/100000000 : ℝ)|^35 ≤ (55643572845309/100000000000000 : ℝ)^27
        have hw : |(63621787/100000000 : ℝ)|=(63621787/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1331673161/2500000000 : ℝ)*x 0 + (5328117889/10000000000 : ℝ)*x 1 + (-948214939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1331673161/2500000000 : ℝ)^35 ≤ (44198552816283/100000000000000 : ℝ)^27 := by
    have hnat : (1331673161 : ℕ)^35*100000000000000^27 ≤ 44198552816283^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331673161 2500000000 44198552816283 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5328117889/10000000000 : ℝ)^35 ≤ (22106941748367/50000000000000 : ℝ)^27 := by
    have hnat : (5328117889 : ℕ)^35*50000000000000^27 ≤ 22106941748367^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5328117889 10000000000 22106941748367 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948214939/5000000000 : ℝ)^35 ≤ (5793781839767/50000000000000 : ℝ)^27 := by
    have hnat : (948214939 : ℕ)^35*50000000000000^27 ≤ 5793781839767^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948214939 5000000000 5793781839767 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1331673161/2500000000 : ℝ), (5328117889/10000000000 : ℝ), (-948214939/5000000000 : ℝ)] ![(44198552816283/100000000000000 : ℝ), (22106941748367/50000000000000 : ℝ), (5793781839767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1331673161/2500000000 : ℝ)|^35 ≤ (44198552816283/100000000000000 : ℝ)^27
        have hw : |(1331673161/2500000000 : ℝ)|=(1331673161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5328117889/10000000000 : ℝ)|^35 ≤ (22106941748367/50000000000000 : ℝ)^27
        have hw : |(5328117889/10000000000 : ℝ)|=(5328117889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948214939/5000000000 : ℝ)|^35 ≤ (5793781839767/50000000000000 : ℝ)^27
        have hw : |(-948214939/5000000000 : ℝ)|=(948214939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (499977631/1000000000 : ℝ)*x 0 + (1250278521/2500000000 : ℝ)*x 1 + (2727082251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499977631/1000000000 : ℝ)^35 ≤ (40714653643851/100000000000000 : ℝ)^27 := by
    have hnat : (499977631 : ℕ)^35*100000000000000^27 ≤ 40714653643851^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499977631 1000000000 40714653643851 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250278521/2500000000 : ℝ)^35 ≤ (20364387955379/50000000000000 : ℝ)^27 := by
    have hnat : (1250278521 : ℕ)^35*50000000000000^27 ≤ 20364387955379^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250278521 2500000000 20364387955379 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727082251/10000000000 : ℝ)^35 ≤ (18556570434117/100000000000000 : ℝ)^27 := by
    have hnat : (2727082251 : ℕ)^35*100000000000000^27 ≤ 18556570434117^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727082251 10000000000 18556570434117 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(499977631/1000000000 : ℝ), (1250278521/2500000000 : ℝ), (2727082251/10000000000 : ℝ)] ![(40714653643851/100000000000000 : ℝ), (20364387955379/50000000000000 : ℝ), (18556570434117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(499977631/1000000000 : ℝ)|^35 ≤ (40714653643851/100000000000000 : ℝ)^27
        have hw : |(499977631/1000000000 : ℝ)|=(499977631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250278521/2500000000 : ℝ)|^35 ≤ (20364387955379/50000000000000 : ℝ)^27
        have hw : |(1250278521/2500000000 : ℝ)|=(1250278521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727082251/10000000000 : ℝ)|^35 ≤ (18556570434117/100000000000000 : ℝ)^27
        have hw : |(2727082251/10000000000 : ℝ)|=(2727082251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-927683181/2500000000 : ℝ)*x 0 + (3349894651/10000000000 : ℝ)*x 1 + (22214189/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927683181/2500000000 : ℝ)^35 ≤ (27662547345361/100000000000000 : ℝ)^27 := by
    have hnat : (927683181 : ℕ)^35*100000000000000^27 ≤ 27662547345361^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927683181 2500000000 27662547345361 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3349894651/10000000000 : ℝ)^35 ≤ (4845399986101/20000000000000 : ℝ)^27 := by
    have hnat : (3349894651 : ℕ)^35*20000000000000^27 ≤ 4845399986101^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3349894651 10000000000 4845399986101 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22214189/39062500 : ℝ)^35 ≤ (48110452708457/100000000000000 : ℝ)^27 := by
    have hnat : (22214189 : ℕ)^35*100000000000000^27 ≤ 48110452708457^27*39062500^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22214189 39062500 48110452708457 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-927683181/2500000000 : ℝ), (3349894651/10000000000 : ℝ), (22214189/39062500 : ℝ)] ![(27662547345361/100000000000000 : ℝ), (4845399986101/20000000000000 : ℝ), (48110452708457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-927683181/2500000000 : ℝ)|^35 ≤ (27662547345361/100000000000000 : ℝ)^27
        have hw : |(-927683181/2500000000 : ℝ)|=(927683181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3349894651/10000000000 : ℝ)|^35 ≤ (4845399986101/20000000000000 : ℝ)^27
        have hw : |(3349894651/10000000000 : ℝ)|=(3349894651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22214189/39062500 : ℝ)|^35 ≤ (48110452708457/100000000000000 : ℝ)^27
        have hw : |(22214189/39062500 : ℝ)|=(22214189/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1509029851/5000000000 : ℝ)*x 0 + (-170286147/625000000 : ℝ)*x 1 + (6769328263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1509029851/5000000000 : ℝ)^35 ≤ (4232559813463/20000000000000 : ℝ)^27 := by
    have hnat : (1509029851 : ℕ)^35*20000000000000^27 ≤ 4232559813463^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509029851 5000000000 4232559813463 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170286147/625000000 : ℝ)^35 ≤ (9267243630593/50000000000000 : ℝ)^27 := by
    have hnat : (170286147 : ℕ)^35*50000000000000^27 ≤ 9267243630593^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170286147 625000000 9267243630593 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6769328263/10000000000 : ℝ)^35 ≤ (6030271366189/10000000000000 : ℝ)^27 := by
    have hnat : (6769328263 : ℕ)^35*10000000000000^27 ≤ 6030271366189^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6769328263 10000000000 6030271366189 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1509029851/5000000000 : ℝ), (-170286147/625000000 : ℝ), (6769328263/10000000000 : ℝ)] ![(4232559813463/20000000000000 : ℝ), (9267243630593/50000000000000 : ℝ), (6030271366189/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1509029851/5000000000 : ℝ)|^35 ≤ (4232559813463/20000000000000 : ℝ)^27
        have hw : |(1509029851/5000000000 : ℝ)|=(1509029851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-170286147/625000000 : ℝ)|^35 ≤ (9267243630593/50000000000000 : ℝ)^27
        have hw : |(-170286147/625000000 : ℝ)|=(170286147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6769328263/10000000000 : ℝ)|^35 ≤ (6030271366189/10000000000000 : ℝ)^27
        have hw : |(6769328263/10000000000 : ℝ)|=(6769328263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2551608591/5000000000 : ℝ)*x 0 + (5929809219/10000000000 : ℝ)*x 1 + (-1341577029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2551608591/5000000000 : ℝ)^35 ≤ (8361983793711/20000000000000 : ℝ)^27 := by
    have hnat : (2551608591 : ℕ)^35*20000000000000^27 ≤ 8361983793711^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2551608591 5000000000 8361983793711 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5929809219/10000000000 : ℝ)^35 ≤ (2031671640597/4000000000000 : ℝ)^27 := by
    have hnat : (5929809219 : ℕ)^35*4000000000000^27 ≤ 2031671640597^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5929809219 10000000000 2031671640597 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1341577029/10000000000 : ℝ)^35 ≤ (7398289999027/100000000000000 : ℝ)^27 := by
    have hnat : (1341577029 : ℕ)^35*100000000000000^27 ≤ 7398289999027^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341577029 10000000000 7398289999027 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2551608591/5000000000 : ℝ), (5929809219/10000000000 : ℝ), (-1341577029/10000000000 : ℝ)] ![(8361983793711/20000000000000 : ℝ), (2031671640597/4000000000000 : ℝ), (7398289999027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2551608591/5000000000 : ℝ)|^35 ≤ (8361983793711/20000000000000 : ℝ)^27
        have hw : |(2551608591/5000000000 : ℝ)|=(2551608591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5929809219/10000000000 : ℝ)|^35 ≤ (2031671640597/4000000000000 : ℝ)^27
        have hw : |(5929809219/10000000000 : ℝ)|=(5929809219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1341577029/10000000000 : ℝ)|^35 ≤ (7398289999027/100000000000000 : ℝ)^27
        have hw : |(-1341577029/10000000000 : ℝ)|=(1341577029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4924737799/10000000000 : ℝ)*x 0 + (1430605173/2500000000 : ℝ)*x 1 + (378958511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4924737799/10000000000 : ℝ)^35 ≤ (39924305356937/100000000000000 : ℝ)^27 := by
    have hnat : (4924737799 : ℕ)^35*100000000000000^27 ≤ 39924305356937^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4924737799 10000000000 39924305356937 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1430605173/2500000000 : ℝ)^35 ≤ (9700219583323/20000000000000 : ℝ)^27 := by
    have hnat : (1430605173 : ℕ)^35*20000000000000^27 ≤ 9700219583323^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430605173 2500000000 9700219583323 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378958511/2000000000 : ℝ)^35 ≤ (11574596711997/100000000000000 : ℝ)^27 := by
    have hnat : (378958511 : ℕ)^35*100000000000000^27 ≤ 11574596711997^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378958511 2000000000 11574596711997 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4924737799/10000000000 : ℝ), (1430605173/2500000000 : ℝ), (378958511/2000000000 : ℝ)] ![(39924305356937/100000000000000 : ℝ), (9700219583323/20000000000000 : ℝ), (11574596711997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4924737799/10000000000 : ℝ)|^35 ≤ (39924305356937/100000000000000 : ℝ)^27
        have hw : |(4924737799/10000000000 : ℝ)|=(4924737799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1430605173/2500000000 : ℝ)|^35 ≤ (9700219583323/20000000000000 : ℝ)^27
        have hw : |(1430605173/2500000000 : ℝ)|=(1430605173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(378958511/2000000000 : ℝ)|^35 ≤ (11574596711997/100000000000000 : ℝ)^27
        have hw : |(378958511/2000000000 : ℝ)|=(378958511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-837754563/2500000000 : ℝ)*x 0 + (74192823/200000000 : ℝ)*x 1 + (2843416817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837754563/2500000000 : ℝ)^35 ≤ (24237534249473/100000000000000 : ℝ)^27 := by
    have hnat : (837754563 : ℕ)^35*100000000000000^27 ≤ 24237534249473^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837754563 2500000000 24237534249473 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74192823/200000000 : ℝ)^35 ≤ (3456499915409/12500000000000 : ℝ)^27 := by
    have hnat : (74192823 : ℕ)^35*12500000000000^27 ≤ 3456499915409^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74192823 200000000 3456499915409 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2843416817/5000000000 : ℝ)^35 ≤ (12027616604187/25000000000000 : ℝ)^27 := by
    have hnat : (2843416817 : ℕ)^35*25000000000000^27 ≤ 12027616604187^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843416817 5000000000 12027616604187 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-837754563/2500000000 : ℝ), (74192823/200000000 : ℝ), (2843416817/5000000000 : ℝ)] ![(24237534249473/100000000000000 : ℝ), (3456499915409/12500000000000 : ℝ), (12027616604187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-837754563/2500000000 : ℝ)|^35 ≤ (24237534249473/100000000000000 : ℝ)^27
        have hw : |(-837754563/2500000000 : ℝ)|=(837754563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(74192823/200000000 : ℝ)|^35 ≤ (3456499915409/12500000000000 : ℝ)^27
        have hw : |(74192823/200000000 : ℝ)|=(74192823/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2843416817/5000000000 : ℝ)|^35 ≤ (12027616604187/25000000000000 : ℝ)^27
        have hw : |(2843416817/5000000000 : ℝ)|=(2843416817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (545098441/2000000000 : ℝ)*x 0 + (-3017171879/10000000000 : ℝ)*x 1 + (1353865837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545098441/2000000000 : ℝ)^35 ≤ (9271273152109/50000000000000 : ℝ)^27 := by
    have hnat : (545098441 : ℕ)^35*50000000000000^27 ≤ 9271273152109^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545098441 2000000000 9271273152109 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3017171879/10000000000 : ℝ)^35 ≤ (21154729374087/100000000000000 : ℝ)^27 := by
    have hnat : (3017171879 : ℕ)^35*100000000000000^27 ≤ 21154729374087^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017171879 10000000000 21154729374087 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353865837/2000000000 : ℝ)^35 ≤ (60302724308871/100000000000000 : ℝ)^27 := by
    have hnat : (1353865837 : ℕ)^35*100000000000000^27 ≤ 60302724308871^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353865837 2000000000 60302724308871 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545098441/2000000000 : ℝ), (-3017171879/10000000000 : ℝ), (1353865837/2000000000 : ℝ)] ![(9271273152109/50000000000000 : ℝ), (21154729374087/100000000000000 : ℝ), (60302724308871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545098441/2000000000 : ℝ)|^35 ≤ (9271273152109/50000000000000 : ℝ)^27
        have hw : |(545098441/2000000000 : ℝ)|=(545098441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3017171879/10000000000 : ℝ)|^35 ≤ (21154729374087/100000000000000 : ℝ)^27
        have hw : |(-3017171879/10000000000 : ℝ)|=(3017171879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353865837/2000000000 : ℝ)|^35 ≤ (60302724308871/100000000000000 : ℝ)^27
        have hw : |(1353865837/2000000000 : ℝ)|=(1353865837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5928406089/10000000000 : ℝ)*x 0 + (2552342479/5000000000 : ℝ)*x 1 + (-83848477/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5928406089/10000000000 : ℝ)^35 ≤ (50776212007969/100000000000000 : ℝ)^27 := by
    have hnat : (5928406089 : ℕ)^35*100000000000000^27 ≤ 50776212007969^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5928406089 10000000000 50776212007969 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2552342479/5000000000 : ℝ)^35 ≤ (41825507953603/100000000000000 : ℝ)^27 := by
    have hnat : (2552342479 : ℕ)^35*100000000000000^27 ≤ 41825507953603^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552342479 5000000000 41825507953603 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83848477/625000000 : ℝ)^35 ≤ (7398280012457/100000000000000 : ℝ)^27 := by
    have hnat : (83848477 : ℕ)^35*100000000000000^27 ≤ 7398280012457^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83848477 625000000 7398280012457 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5928406089/10000000000 : ℝ), (2552342479/5000000000 : ℝ), (-83848477/625000000 : ℝ)] ![(50776212007969/100000000000000 : ℝ), (41825507953603/100000000000000 : ℝ), (7398280012457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5928406089/10000000000 : ℝ)|^35 ≤ (50776212007969/100000000000000 : ℝ)^27
        have hw : |(5928406089/10000000000 : ℝ)|=(5928406089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2552342479/5000000000 : ℝ)|^35 ≤ (41825507953603/100000000000000 : ℝ)^27
        have hw : |(2552342479/5000000000 : ℝ)|=(2552342479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83848477/625000000 : ℝ)|^35 ≤ (7398280012457/100000000000000 : ℝ)^27
        have hw : |(-83848477/625000000 : ℝ)|=(83848477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_18 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5721066957/10000000000 : ℝ)*x 0 + (2463077259/5000000000 : ℝ)*x 1 + (236848817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5721066957/10000000000 : ℝ)^35 ≤ (48486225056157/100000000000000 : ℝ)^27 := by
    have hnat : (5721066957 : ℕ)^35*100000000000000^27 ≤ 48486225056157^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5721066957 10000000000 48486225056157 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463077259/5000000000 : ℝ)^35 ≤ (19969597096731/50000000000000 : ℝ)^27 := by
    have hnat : (2463077259 : ℕ)^35*50000000000000^27 ≤ 19969597096731^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463077259 5000000000 19969597096731 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236848817/1250000000 : ℝ)^35 ≤ (1446822590543/12500000000000 : ℝ)^27 := by
    have hnat : (236848817 : ℕ)^35*12500000000000^27 ≤ 1446822590543^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236848817 1250000000 1446822590543 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5721066957/10000000000 : ℝ), (2463077259/5000000000 : ℝ), (236848817/1250000000 : ℝ)] ![(48486225056157/100000000000000 : ℝ), (19969597096731/50000000000000 : ℝ), (1446822590543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5721066957/10000000000 : ℝ)|^35 ≤ (48486225056157/100000000000000 : ℝ)^27
        have hw : |(5721066957/10000000000 : ℝ)|=(5721066957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2463077259/5000000000 : ℝ)|^35 ≤ (19969597096731/50000000000000 : ℝ)^27
        have hw : |(2463077259/5000000000 : ℝ)|=(2463077259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(236848817/1250000000 : ℝ)|^35 ≤ (1446822590543/12500000000000 : ℝ)^27
        have hw : |(236848817/1250000000 : ℝ)|=(236848817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-394889531/1000000000 : ℝ)*x 0 + (1973894169/5000000000 : ℝ)*x 1 + (4935713121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394889531/1000000000 : ℝ)^35 ≤ (29985606745593/100000000000000 : ℝ)^27 := by
    have hnat : (394889531 : ℕ)^35*100000000000000^27 ≤ 29985606745593^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394889531 1000000000 29985606745593 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973894169/5000000000 : ℝ)^35 ≤ (29974710921097/100000000000000 : ℝ)^27 := by
    have hnat : (1973894169 : ℕ)^35*100000000000000^27 ≤ 29974710921097^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973894169 5000000000 29974710921097 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4935713121/10000000000 : ℝ)^35 ≤ (2001984115911/5000000000000 : ℝ)^27 := by
    have hnat : (4935713121 : ℕ)^35*5000000000000^27 ≤ 2001984115911^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4935713121 10000000000 2001984115911 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-394889531/1000000000 : ℝ), (1973894169/5000000000 : ℝ), (4935713121/10000000000 : ℝ)] ![(29985606745593/100000000000000 : ℝ), (29974710921097/100000000000000 : ℝ), (2001984115911/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-394889531/1000000000 : ℝ)|^35 ≤ (29985606745593/100000000000000 : ℝ)^27
        have hw : |(-394889531/1000000000 : ℝ)|=(394889531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1973894169/5000000000 : ℝ)|^35 ≤ (29974710921097/100000000000000 : ℝ)^27
        have hw : |(1973894169/5000000000 : ℝ)|=(1973894169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4935713121/10000000000 : ℝ)|^35 ≤ (2001984115911/5000000000000 : ℝ)^27
        have hw : |(4935713121/10000000000 : ℝ)|=(4935713121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3052912741/10000000000 : ℝ)*x 0 + (-1525982059/5000000000 : ℝ)*x 1 + (1297146529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3052912741/10000000000 : ℝ)^35 ≤ (10740071641927/50000000000000 : ℝ)^27 := by
    have hnat : (3052912741 : ℕ)^35*50000000000000^27 ≤ 10740071641927^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3052912741 10000000000 10740071641927 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1525982059/5000000000 : ℝ)^35 ≤ (5367872899613/25000000000000 : ℝ)^27 := by
    have hnat : (1525982059 : ℕ)^35*25000000000000^27 ≤ 5367872899613^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525982059 5000000000 5367872899613 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297146529/2000000000 : ℝ)^35 ≤ (57048365100561/100000000000000 : ℝ)^27 := by
    have hnat : (1297146529 : ℕ)^35*100000000000000^27 ≤ 57048365100561^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297146529 2000000000 57048365100561 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3052912741/10000000000 : ℝ), (-1525982059/5000000000 : ℝ), (1297146529/2000000000 : ℝ)] ![(10740071641927/50000000000000 : ℝ), (5367872899613/25000000000000 : ℝ), (57048365100561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3052912741/10000000000 : ℝ)|^35 ≤ (10740071641927/50000000000000 : ℝ)^27
        have hw : |(3052912741/10000000000 : ℝ)|=(3052912741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1525982059/5000000000 : ℝ)|^35 ≤ (5367872899613/25000000000000 : ℝ)^27
        have hw : |(-1525982059/5000000000 : ℝ)|=(1525982059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297146529/2000000000 : ℝ)|^35 ≤ (57048365100561/100000000000000 : ℝ)^27
        have hw : |(1297146529/2000000000 : ℝ)|=(1297146529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5659328561/10000000000 : ℝ)*x 0 + (305995567/625000000 : ℝ)*x 1 + (-2019195979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5659328561/10000000000 : ℝ)^35 ≤ (5976130593271/12500000000000 : ℝ)^27 := by
    have hnat : (5659328561 : ℕ)^35*12500000000000^27 ≤ 5976130593271^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5659328561 10000000000 5976130593271 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305995567/625000000 : ℝ)^35 ≤ (19810909585131/50000000000000 : ℝ)^27 := by
    have hnat : (305995567 : ℕ)^35*50000000000000^27 ≤ 19810909585131^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305995567 625000000 19810909585131 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2019195979/10000000000 : ℝ)^35 ≤ (12569136063763/100000000000000 : ℝ)^27 := by
    have hnat : (2019195979 : ℕ)^35*100000000000000^27 ≤ 12569136063763^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019195979 10000000000 12569136063763 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5659328561/10000000000 : ℝ), (305995567/625000000 : ℝ), (-2019195979/10000000000 : ℝ)] ![(5976130593271/12500000000000 : ℝ), (19810909585131/50000000000000 : ℝ), (12569136063763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5659328561/10000000000 : ℝ)|^35 ≤ (5976130593271/12500000000000 : ℝ)^27
        have hw : |(5659328561/10000000000 : ℝ)|=(5659328561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(305995567/625000000 : ℝ)|^35 ≤ (19810909585131/50000000000000 : ℝ)^27
        have hw : |(305995567/625000000 : ℝ)|=(305995567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2019195979/10000000000 : ℝ)|^35 ≤ (12569136063763/100000000000000 : ℝ)^27
        have hw : |(-2019195979/10000000000 : ℝ)|=(2019195979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308051_s2_s2_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4320548883/10000000000 : ℝ)*x 0 + (297709921/500000000 : ℝ)*x 1 + (234318239/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320548883/10000000000 : ℝ)^35 ≤ (16846917932277/50000000000000 : ℝ)^27 := by
    have hnat : (4320548883 : ℕ)^35*50000000000000^27 ≤ 16846917932277^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320548883 10000000000 16846917932277 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297709921/500000000 : ℝ)^35 ≤ (25531379802929/50000000000000 : ℝ)^27 := by
    have hnat : (297709921 : ℕ)^35*50000000000000^27 ≤ 25531379802929^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297709921 500000000 25531379802929 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234318239/1000000000 : ℝ)^35 ≤ (7621702258161/50000000000000 : ℝ)^27 := by
    have hnat : (234318239 : ℕ)^35*50000000000000^27 ≤ 7621702258161^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234318239 1000000000 7621702258161 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320548883/10000000000 : ℝ), (297709921/500000000 : ℝ), (234318239/1000000000 : ℝ)] ![(16846917932277/50000000000000 : ℝ), (25531379802929/50000000000000 : ℝ), (7621702258161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320548883/10000000000 : ℝ)|^35 ≤ (16846917932277/50000000000000 : ℝ)^27
        have hw : |(4320548883/10000000000 : ℝ)|=(4320548883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(297709921/500000000 : ℝ)|^35 ≤ (25531379802929/50000000000000 : ℝ)^27
        have hw : |(297709921/500000000 : ℝ)|=(297709921/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(234318239/1000000000 : ℝ)|^35 ≤ (7621702258161/50000000000000 : ℝ)^27
        have hw : |(234318239/1000000000 : ℝ)|=(234318239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308051_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((7711/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7711/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61567/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61567/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16931/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16931/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29507/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29507/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14749/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14749/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(557/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(557/12500 : ℝ)*X 1 2) := by
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
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (7711/12500 : ℝ) ^ (17/4 : ℝ) ≤ (3208432756851536541/25000000000000000000 : ℝ) := by
    have hpowers : (7711/12500 : ℝ)^17 ≤ (3208432756851536541/25000000000000000000 : ℝ)^4 := by
      have hnat : (7711 : ℕ)^17*25000000000000000000^4 ≤ 3208432756851536541^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7711 12500 3208432756851536541 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7711/12500 : ℝ)) (X := (3208432756851536541/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (28208432756851536541/25000000000000000000 : ℝ) ≤ (10288180527358691/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (28208432756851536541/25000000000000000000 : ℝ)^4 ≤ (10288180527358691/10000000000000000 : ℝ)^17 := by
      have hnat : (28208432756851536541 : ℕ)^4*10000000000000000^17 ≤ 10288180527358691^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28208432756851536541 25000000000000000000 10288180527358691 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10288180527358691/10000000000000000 : ℝ)) (X := (28208432756851536541/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (15708432756851536541/12500000000000000000 : ℝ) ≤ (527614297760363/500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (15708432756851536541/12500000000000000000 : ℝ)^4 ≤ (527614297760363/500000000000000 : ℝ)^17 := by
      have hnat : (15708432756851536541 : ℕ)^4*500000000000000^17 ≤ 527614297760363^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15708432756851536541 12500000000000000000 527614297760363 500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (527614297760363/500000000000000 : ℝ)) (X := (15708432756851536541/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(26198229759881/560800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(264105427848569/6168800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (7711/12500 : ℝ)) (alpha := (26198229759881/560800000000000 : ℝ)) (beta := (264105427848569/6168800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7711/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(26198229759881/560800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(264105427848569/6168800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (61567/100000 : ℝ) ^ (17/4 : ℝ) ≤ (6363542817183288653/50000000000000000000 : ℝ) := by
    have hpowers : (61567/100000 : ℝ)^17 ≤ (6363542817183288653/50000000000000000000 : ℝ)^4 := by
      have hnat : (61567 : ℕ)^17*50000000000000000000^4 ≤ 6363542817183288653^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61567 100000 6363542817183288653 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61567/100000 : ℝ)) (X := (6363542817183288653/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (56363542817183288653/50000000000000000000 : ℝ) ≤ (5142945858522331/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (56363542817183288653/50000000000000000000 : ℝ)^4 ≤ (5142945858522331/5000000000000000 : ℝ)^17 := by
      have hnat : (56363542817183288653 : ℕ)^4*5000000000000000^17 ≤ 5142945858522331^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56363542817183288653 50000000000000000000 5142945858522331 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5142945858522331/5000000000000000 : ℝ)) (X := (56363542817183288653/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (31363542817183288653/25000000000000000000 : ℝ) ≤ (10548069097959443/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (31363542817183288653/25000000000000000000 : ℝ)^4 ≤ (10548069097959443/10000000000000000 : ℝ)^17 := by
      have hnat : (31363542817183288653 : ℕ)^4*10000000000000000^17 ≤ 10548069097959443^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31363542817183288653 25000000000000000000 10548069097959443 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10548069097959443/10000000000000000 : ℝ)) (X := (31363542817183288653/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(142945858522331/3078350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(9040599341889/212300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (61567/100000 : ℝ)) (alpha := (142945858522331/3078350000000000 : ℝ)) (beta := (9040599341889/212300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (61567/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(142945858522331/3078350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(9040599341889/212300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (16931/100000 : ℝ) ^ (17/4 : ℝ) ≤ (52710980073794591/100000000000000000000 : ℝ) := by
    have hpowers : (16931/100000 : ℝ)^17 ≤ (52710980073794591/100000000000000000000 : ℝ)^4 := by
      have hnat : (16931 : ℕ)^17*100000000000000000000^4 ≤ 52710980073794591^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16931 100000 52710980073794591 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16931/100000 : ℝ)) (X := (52710980073794591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (100052710980073794591/100000000000000000000 : ℝ) ≤ (10001240008468027/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100052710980073794591/100000000000000000000 : ℝ)^4 ≤ (10001240008468027/10000000000000000 : ℝ)^17 := by
      have hnat : (100052710980073794591 : ℕ)^4*10000000000000000^17 ≤ 10001240008468027^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052710980073794591 100000000000000000000 10001240008468027 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001240008468027/10000000000000000 : ℝ)) (X := (100052710980073794591/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (50052710980073794591/50000000000000000000 : ℝ) ≤ (10002479517472433/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50052710980073794591/50000000000000000000 : ℝ)^4 ≤ (10002479517472433/10000000000000000 : ℝ)^17 := by
      have hnat : (50052710980073794591 : ℕ)^4*10000000000000000^17 ≤ 10002479517472433^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50052710980073794591 50000000000000000000 10002479517472433 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002479517472433/10000000000000000 : ℝ)) (X := (50052710980073794591/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1240008468027/1693100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(619754502203/846550000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (16931/100000 : ℝ)) (alpha := (1240008468027/1693100000000000 : ℝ)) (beta := (619754502203/846550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (16931/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1240008468027/1693100000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(619754502203/846550000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-770665641/2000000000 : ℝ)*X 0 0+(3852197669/10000000000 : ℝ)*X 0 1+(102261127/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((7824071/25000000 : ℝ)*X 1 0+(-195544387/625000000 : ℝ)*X 1 1+(63621787/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1331673161/2500000000 : ℝ)*X 2 0+(5328117889/10000000000 : ℝ)*X 2 1+(-948214939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((499977631/1000000000 : ℝ)*X 0 0+(1250278521/2500000000 : ℝ)*X 0 1+(2727082251/10000000000 : ℝ)*X 0 2+(499977631/1000000000 : ℝ)*X 1 0+(1250278521/2500000000 : ℝ)*X 1 1+(2727082251/10000000000 : ℝ)*X 1 2+(499977631/1000000000 : ℝ)*X 2 0+(1250278521/2500000000 : ℝ)*X 2 1+(2727082251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-927683181/2500000000 : ℝ)*X 0 0+(3349894651/10000000000 : ℝ)*X 0 1+(22214189/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1509029851/5000000000 : ℝ)*X 1 0+(-170286147/625000000 : ℝ)*X 1 1+(6769328263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2551608591/5000000000 : ℝ)*X 2 0+(5929809219/10000000000 : ℝ)*X 2 1+(-1341577029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((4924737799/10000000000 : ℝ)*X 0 0+(1430605173/2500000000 : ℝ)*X 0 1+(378958511/2000000000 : ℝ)*X 0 2+(4924737799/10000000000 : ℝ)*X 1 0+(1430605173/2500000000 : ℝ)*X 1 1+(378958511/2000000000 : ℝ)*X 1 2+(4924737799/10000000000 : ℝ)*X 2 0+(1430605173/2500000000 : ℝ)*X 2 1+(378958511/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-837754563/2500000000 : ℝ)*X 0 0+(74192823/200000000 : ℝ)*X 0 1+(2843416817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((545098441/2000000000 : ℝ)*X 1 0+(-3017171879/10000000000 : ℝ)*X 1 1+(1353865837/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((5928406089/10000000000 : ℝ)*X 2 0+(2552342479/5000000000 : ℝ)*X 2 1+(-83848477/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((5721066957/10000000000 : ℝ)*X 0 0+(2463077259/5000000000 : ℝ)*X 0 1+(236848817/1250000000 : ℝ)*X 0 2+(5721066957/10000000000 : ℝ)*X 1 0+(2463077259/5000000000 : ℝ)*X 1 1+(236848817/1250000000 : ℝ)*X 1 2+(5721066957/10000000000 : ℝ)*X 2 0+(2463077259/5000000000 : ℝ)*X 2 1+(236848817/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-394889531/1000000000 : ℝ)*X 0 0+(1973894169/5000000000 : ℝ)*X 0 1+(4935713121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3052912741/10000000000 : ℝ)*X 1 0+(-1525982059/5000000000 : ℝ)*X 1 1+(1297146529/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((5659328561/10000000000 : ℝ)*X 2 0+(305995567/625000000 : ℝ)*X 2 1+(-2019195979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((4320548883/10000000000 : ℝ)*X 0 0+(297709921/500000000 : ℝ)*X 0 1+(234318239/1000000000 : ℝ)*X 0 2+(4320548883/10000000000 : ℝ)*X 1 0+(297709921/500000000 : ℝ)*X 1 1+(234318239/1000000000 : ℝ)*X 1 2+(4320548883/10000000000 : ℝ)*X 2 0+(297709921/500000000 : ℝ)*X 2 1+(234318239/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308051_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((29507/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29507/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15358496679571331144842885323/1328574554140000000000000000000000 : ℝ) := by norm_num
    linear_combination (246111176289/500000000000 : ℝ)*(base49) + (455894824131/1000000000000 : ℝ)*(base59) + (939618996817/500000000000 : ℝ)*(base60) + (317430519877/40000000000 : ℝ)*(major_s2_0) + (317430519877/40000000000 : ℝ)*(major_s2_1) + (317430519877/40000000000 : ℝ)*(major_s2_2) + (2908509/62500000000 : ℝ)*(sp_s2_2) + (5403787246787/500000000000 : ℝ)*(sp_s2_7) + (5403697897837/500000000000 : ℝ)*(sp_s2_8) + (1080752795743/100000000000 : ℝ)*(sp_s2_9) + (5063858054679/1000000000000 : ℝ)*(sp_s2_12) + (128870003/1000000000000 : ℝ)*(sp_s2_14) + (49827897/1000000000000 : ℝ)*(sp_s2_20) + (11199027/125000000000 : ℝ)*(sp_s2_25) + (1012789529379/200000000000 : ℝ)*(f.failure) + (5403787246787/500000000000 : ℝ)*(f.sum) + (9061917240306098437/20847817540000000000000000000000 : ℝ)*base62 + (44385814249767/169310000000000000000000000 : ℝ)*base64 + (19835955051511/42460000000000000000000000 : ℝ)*base66 + (228150626308313/338620000000000000000000000 : ℝ)*base68 + (64526884829730557/1898980960000000000000000000000 : ℝ)*base70 + (378350336846527/1233760000000000000000000000 : ℝ)*base72 + (1407244237803/3847937500000000000000000 : ℝ)*base74 + (47348768695999/112160000000000000000000000 : ℝ)*base76 + (50470479794444519/238115680000000000000000000000 : ℝ)*base78 + (12469/20000000000000000 : ℝ)*base87 + (12469/20000000000000000 : ℝ)*base89 + (12469/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14749/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14749/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37490712046901984505619401/4738140350000000000000000000000 : ℝ) := by norm_num
    linear_combination (492220621221/1000000000000 : ℝ)*(base49) + (236108591971/250000000000 : ℝ)*(base59) + (1043600026087/500000000000 : ℝ)*(base60) + (1983907701479/250000000000 : ℝ)*(major_s2_0) + (1983907701479/250000000000 : ℝ)*(major_s2_1) + (1983907701479/250000000000 : ℝ)*(major_s2_2) + (91982061/1000000000000 : ℝ)*(sp_s2_0) + (10855819/500000000000 : ℝ)*(sp_s2_6) + (50983901/500000000000 : ℝ)*(sp_s2_8) + (1350912962341/125000000000 : ℝ)*(sp_s2_13) + (2701823428247/250000000000 : ℝ)*(sp_s2_14) + (1350911244541/125000000000 : ℝ)*(sp_s2_15) + (5063841581887/1000000000000 : ℝ)*(sp_s2_18) + (52862231/500000000000 : ℝ)*(sp_s2_21) + (202554531741/40000000000 : ℝ)*(f.failure) + (1080739568079/100000000000 : ℝ)*(f.sum) + (381344815268591677/592267543750000000000000000000 : ℝ)*base62 + (157640221071063/846550000000000000000000000 : ℝ)*base65 + (1947160072139/4825000000000000000000000 : ℝ)*base67 + (565036338150731/846550000000000000000000000 : ℝ)*base68 + (489185538050962021/2373726200000000000000000000000 : ℝ)*base71 + (51222782677379/140200000000000000000000000 : ℝ)*base72 + (93105529211969/279850000000000000000000000 : ℝ)*base74 + (39733709050921/140200000000000000000000000 : ℝ)*base76 + (1657072915145057/5411720000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (149/4000000000000000 : ℝ)*base86 + (149/4000000000000000 : ℝ)*base88 + (149/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(557/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(557/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7941194785669072675327119/1797225650000000000000000000000 : ℝ) := by norm_num
    linear_combination (139879106913/250000000000 : ℝ)*(base49) + (23130729687/62500000000 : ℝ)*(base60) + (278207212643/62500000000 : ℝ)*(major_s2_0) + (278207212643/62500000000 : ℝ)*(major_s2_1) + (278207212643/62500000000 : ℝ)*(major_s2_2) + (17193383/125000000000 : ℝ)*(sp_s2_1) + (7521249/1000000000000 : ℝ)*(sp_s2_2) + (1260623/200000000000 : ℝ)*(sp_s2_12) + (33777/250000000000 : ℝ)*(sp_s2_14) + (26843211/1000000000000 : ℝ)*(sp_s2_15) + (6062167971443/1000000000000 : ℝ)*(sp_s2_19) + (757753786159/125000000000 : ℝ)*(sp_s2_20) + (6062133606983/1000000000000 : ℝ)*(sp_s2_21) + (11095527567/3906250000 : ℝ)*(sp_s2_25) + (2840461360267/1000000000000 : ℝ)*(f.failure) + (6062167971443/1000000000000 : ℝ)*(f.sum) + (31964293028548259963/52119543850000000000000000000000 : ℝ)*base62 + (67164639140703/423275000000000000000000000 : ℝ)*base64 + (16084199022141/26537500000000000000000000 : ℝ)*base67 + (438835003942303/846550000000000000000000000 : ℝ)*base68 + (144192069810715183/593431550000000000000000000000 : ℝ)*base70 + (26438093955627/96387500000000000000000000 : ℝ)*base72 + (913554589066663/3078350000000000000000000000 : ℝ)*base75 + (2440178349877/8762500000000000000000000 : ℝ)*base77 + (3507567489198621/14882230000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1837/100000000000000000 : ℝ)*base87 + (1837/100000000000000000 : ℝ)*base89 + (1837/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((7711/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7711/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61567/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61567/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16931/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16931/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29507/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29507/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14749/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14749/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(557/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(557/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308051_s2 p hpa hpb X hX hprev1

#print axioms solution
