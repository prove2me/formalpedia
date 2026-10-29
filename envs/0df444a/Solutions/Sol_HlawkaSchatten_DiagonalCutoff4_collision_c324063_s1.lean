-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c324063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:58:32.612652+00:00
-- url     : https://prove2.me/submissions/0b1f494d-f466-460a-86a2-c711584258b4

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
theorem collision_support_c324063_s1_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-948471021/10000000000 : ℝ)*x 0 + (5414213833/10000000000 : ℝ)*x 1 + (1367177593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (948471021/10000000000 : ℝ)^85 ≤ (5493033600003/100000000000000 : ℝ)^69 := by
    have hnat : (948471021 : ℕ)^85*100000000000000^69 ≤ 5493033600003^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948471021 10000000000 5493033600003 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414213833/10000000000 : ℝ)^85 ≤ (11740498056899/25000000000000 : ℝ)^69 := by
    have hnat : (5414213833 : ℕ)^85*25000000000000^69 ≤ 11740498056899^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414213833 10000000000 11740498056899 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367177593/2500000000 : ℝ)^85 ≤ (23772487080589/50000000000000 : ℝ)^69 := by
    have hnat : (1367177593 : ℕ)^85*50000000000000^69 ≤ 23772487080589^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367177593 2500000000 23772487080589 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-948471021/10000000000 : ℝ), (5414213833/10000000000 : ℝ), (1367177593/2500000000 : ℝ)] ![(5493033600003/100000000000000 : ℝ), (11740498056899/25000000000000 : ℝ), (23772487080589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-948471021/10000000000 : ℝ)|^85 ≤ (5493033600003/100000000000000 : ℝ)^69
        have hw : |(-948471021/10000000000 : ℝ)|=(948471021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414213833/10000000000 : ℝ)|^85 ≤ (11740498056899/25000000000000 : ℝ)^69
        have hw : |(5414213833/10000000000 : ℝ)|=(5414213833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367177593/2500000000 : ℝ)|^85 ≤ (23772487080589/50000000000000 : ℝ)^69
        have hw : |(1367177593/2500000000 : ℝ)|=(1367177593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2706998647/5000000000 : ℝ)*x 0 + (-94570427/1000000000 : ℝ)*x 1 + (5470768749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706998647/5000000000 : ℝ)^85 ≤ (11739919621231/25000000000000 : ℝ)^69 := by
    have hnat : (2706998647 : ℕ)^85*25000000000000^69 ≤ 11739919621231^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706998647 5000000000 11739919621231 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94570427/1000000000 : ℝ)^85 ≤ (342081321673/6250000000000 : ℝ)^69 := by
    have hnat : (94570427 : ℕ)^85*6250000000000^69 ≤ 342081321673^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94570427 1000000000 342081321673 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470768749/10000000000 : ℝ)^85 ≤ (11891755085917/25000000000000 : ℝ)^69 := by
    have hnat : (5470768749 : ℕ)^85*25000000000000^69 ≤ 11891755085917^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470768749 10000000000 11891755085917 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706998647/5000000000 : ℝ), (-94570427/1000000000 : ℝ), (5470768749/10000000000 : ℝ)] ![(11739919621231/25000000000000 : ℝ), (342081321673/6250000000000 : ℝ), (11891755085917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706998647/5000000000 : ℝ)|^85 ≤ (11739919621231/25000000000000 : ℝ)^69
        have hw : |(2706998647/5000000000 : ℝ)|=(2706998647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-94570427/1000000000 : ℝ)|^85 ≤ (342081321673/6250000000000 : ℝ)^69
        have hw : |(-94570427/1000000000 : ℝ)|=(94570427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470768749/10000000000 : ℝ)|^85 ≤ (11891755085917/25000000000000 : ℝ)^69
        have hw : |(5470768749/10000000000 : ℝ)|=(5470768749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2722019987/5000000000 : ℝ)*x 0 + (1092513871/2000000000 : ℝ)*x 1 + (-182566577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2722019987/5000000000 : ℝ)^85 ≤ (47280892520901/100000000000000 : ℝ)^69 := by
    have hnat : (2722019987 : ℕ)^85*100000000000000^69 ≤ 47280892520901^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722019987 5000000000 47280892520901 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092513871/2000000000 : ℝ)^85 ≤ (9495842485203/20000000000000 : ℝ)^69 := by
    have hnat : (1092513871 : ℕ)^85*20000000000000^69 ≤ 9495842485203^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092513871 2000000000 9495842485203 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182566577/2000000000 : ℝ)^85 ≤ (1309973760491/25000000000000 : ℝ)^69 := by
    have hnat : (182566577 : ℕ)^85*25000000000000^69 ≤ 1309973760491^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182566577 2000000000 1309973760491 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2722019987/5000000000 : ℝ), (1092513871/2000000000 : ℝ), (-182566577/2000000000 : ℝ)] ![(47280892520901/100000000000000 : ℝ), (9495842485203/20000000000000 : ℝ), (1309973760491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2722019987/5000000000 : ℝ)|^85 ≤ (47280892520901/100000000000000 : ℝ)^69
        have hw : |(2722019987/5000000000 : ℝ)|=(2722019987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092513871/2000000000 : ℝ)|^85 ≤ (9495842485203/20000000000000 : ℝ)^69
        have hw : |(1092513871/2000000000 : ℝ)|=(1092513871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-182566577/2000000000 : ℝ)|^85 ≤ (1309973760491/25000000000000 : ℝ)^69
        have hw : |(-182566577/2000000000 : ℝ)|=(182566577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4160936417/10000000000 : ℝ)*x 0 + (1028223813/2500000000 : ℝ)*x 1 + (4023228187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4160936417/10000000000 : ℝ)^85 ≤ (3395373553351/10000000000000 : ℝ)^69 := by
    have hnat : (4160936417 : ℕ)^85*10000000000000^69 ≤ 3395373553351^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160936417 10000000000 3395373553351 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028223813/2500000000 : ℝ)^85 ≤ (16735729369821/50000000000000 : ℝ)^69 := by
    have hnat : (1028223813 : ℕ)^85*50000000000000^69 ≤ 16735729369821^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028223813 2500000000 16735729369821 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023228187/10000000000 : ℝ)^85 ≤ (32574805711009/100000000000000 : ℝ)^69 := by
    have hnat : (4023228187 : ℕ)^85*100000000000000^69 ≤ 32574805711009^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023228187 10000000000 32574805711009 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4160936417/10000000000 : ℝ), (1028223813/2500000000 : ℝ), (4023228187/10000000000 : ℝ)] ![(3395373553351/10000000000000 : ℝ), (16735729369821/50000000000000 : ℝ), (32574805711009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4160936417/10000000000 : ℝ)|^85 ≤ (3395373553351/10000000000000 : ℝ)^69
        have hw : |(4160936417/10000000000 : ℝ)|=(4160936417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028223813/2500000000 : ℝ)|^85 ≤ (16735729369821/50000000000000 : ℝ)^69
        have hw : |(1028223813/2500000000 : ℝ)|=(1028223813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023228187/10000000000 : ℝ)|^85 ≤ (32574805711009/100000000000000 : ℝ)^69
        have hw : |(4023228187/10000000000 : ℝ)|=(4023228187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-790684007/10000000000 : ℝ)*x 0 + (2313858231/5000000000 : ℝ)*x 1 + (632757959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (790684007/10000000000 : ℝ)^85 ≤ (2195014593869/50000000000000 : ℝ)^69 := by
    have hnat : (790684007 : ℕ)^85*50000000000000^69 ≤ 2195014593869^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790684007 10000000000 2195014593869 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2313858231/5000000000 : ℝ)^85 ≤ (38705316606099/100000000000000 : ℝ)^69 := by
    have hnat : (2313858231 : ℕ)^85*100000000000000^69 ≤ 38705316606099^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313858231 5000000000 38705316606099 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632757959/1000000000 : ℝ)^85 ≤ (56904654191691/100000000000000 : ℝ)^69 := by
    have hnat : (632757959 : ℕ)^85*100000000000000^69 ≤ 56904654191691^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632757959 1000000000 56904654191691 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-790684007/10000000000 : ℝ), (2313858231/5000000000 : ℝ), (632757959/1000000000 : ℝ)] ![(2195014593869/50000000000000 : ℝ), (38705316606099/100000000000000 : ℝ), (56904654191691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-790684007/10000000000 : ℝ)|^85 ≤ (2195014593869/50000000000000 : ℝ)^69
        have hw : |(-790684007/10000000000 : ℝ)|=(790684007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2313858231/5000000000 : ℝ)|^85 ≤ (38705316606099/100000000000000 : ℝ)^69
        have hw : |(2313858231/5000000000 : ℝ)|=(2313858231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(632757959/1000000000 : ℝ)|^85 ≤ (56904654191691/100000000000000 : ℝ)^69
        have hw : |(632757959/1000000000 : ℝ)|=(632757959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2487034809/5000000000 : ℝ)*x 0 + (-38408237/2000000000 : ℝ)*x 1 + (3164832981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2487034809/5000000000 : ℝ)^85 ≤ (10576066754443/25000000000000 : ℝ)^69 := by
    have hnat : (2487034809 : ℕ)^85*25000000000000^69 ≤ 10576066754443^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487034809 5000000000 10576066754443 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38408237/2000000000 : ℝ)^85 ≤ (383982033047/50000000000000 : ℝ)^69 := by
    have hnat : (38408237 : ℕ)^85*50000000000000^69 ≤ 383982033047^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38408237 2000000000 383982033047 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3164832981/5000000000 : ℝ)^85 ≤ (56927768896609/100000000000000 : ℝ)^69 := by
    have hnat : (3164832981 : ℕ)^85*100000000000000^69 ≤ 56927768896609^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3164832981 5000000000 56927768896609 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2487034809/5000000000 : ℝ), (-38408237/2000000000 : ℝ), (3164832981/5000000000 : ℝ)] ![(10576066754443/25000000000000 : ℝ), (383982033047/50000000000000 : ℝ), (56927768896609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2487034809/5000000000 : ℝ)|^85 ≤ (10576066754443/25000000000000 : ℝ)^69
        have hw : |(2487034809/5000000000 : ℝ)|=(2487034809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38408237/2000000000 : ℝ)|^85 ≤ (383982033047/50000000000000 : ℝ)^69
        have hw : |(-38408237/2000000000 : ℝ)|=(38408237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3164832981/5000000000 : ℝ)|^85 ≤ (56927768896609/100000000000000 : ℝ)^69
        have hw : |(3164832981/5000000000 : ℝ)|=(3164832981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4719765747/10000000000 : ℝ)*x 0 + (263564913/400000000 : ℝ)*x 1 + (-141726751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4719765747/10000000000 : ℝ)^85 ≤ (2478493651493/6250000000000 : ℝ)^69 := by
    have hnat : (4719765747 : ℕ)^85*6250000000000^69 ≤ 2478493651493^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719765747 10000000000 2478493651493 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263564913/400000000 : ℝ)^85 ≤ (11963179199809/20000000000000 : ℝ)^69 := by
    have hnat : (263564913 : ℕ)^85*20000000000000^69 ≤ 11963179199809^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263564913 400000000 11963179199809 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141726751/10000000000 : ℝ)^85 ≤ (264102787431/50000000000000 : ℝ)^69 := by
    have hnat : (141726751 : ℕ)^85*50000000000000^69 ≤ 264102787431^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141726751 10000000000 264102787431 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4719765747/10000000000 : ℝ), (263564913/400000000 : ℝ), (-141726751/10000000000 : ℝ)] ![(2478493651493/6250000000000 : ℝ), (11963179199809/20000000000000 : ℝ), (264102787431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4719765747/10000000000 : ℝ)|^85 ≤ (2478493651493/6250000000000 : ℝ)^69
        have hw : |(4719765747/10000000000 : ℝ)|=(4719765747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263564913/400000000 : ℝ)|^85 ≤ (11963179199809/20000000000000 : ℝ)^69
        have hw : |(263564913/400000000 : ℝ)|=(263564913/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141726751/10000000000 : ℝ)|^85 ≤ (264102787431/50000000000000 : ℝ)^69
        have hw : |(-141726751/10000000000 : ℝ)|=(141726751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1124702471/2500000000 : ℝ)*x 0 + (582171341/1000000000 : ℝ)*x 1 + (84957191/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124702471/2500000000 : ℝ)^85 ≤ (37381481887813/100000000000000 : ℝ)^69 := by
    have hnat : (1124702471 : ℕ)^85*100000000000000^69 ≤ 37381481887813^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124702471 2500000000 37381481887813 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582171341/1000000000 : ℝ)^85 ≤ (10270695393843/20000000000000 : ℝ)^69 := by
    have hnat : (582171341 : ℕ)^85*20000000000000^69 ≤ 10270695393843^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582171341 1000000000 10270695393843 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84957191/500000000 : ℝ)^85 ≤ (11265041123411/100000000000000 : ℝ)^69 := by
    have hnat : (84957191 : ℕ)^85*100000000000000^69 ≤ 11265041123411^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84957191 500000000 11265041123411 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124702471/2500000000 : ℝ), (582171341/1000000000 : ℝ), (84957191/500000000 : ℝ)] ![(37381481887813/100000000000000 : ℝ), (10270695393843/20000000000000 : ℝ), (11265041123411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124702471/2500000000 : ℝ)|^85 ≤ (37381481887813/100000000000000 : ℝ)^69
        have hw : |(1124702471/2500000000 : ℝ)|=(1124702471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582171341/1000000000 : ℝ)|^85 ≤ (10270695393843/20000000000000 : ℝ)^69
        have hw : |(582171341/1000000000 : ℝ)|=(582171341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84957191/500000000 : ℝ)|^85 ≤ (11265041123411/100000000000000 : ℝ)^69
        have hw : |(84957191/500000000 : ℝ)|=(84957191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19668091/1000000000 : ℝ)*x 0 + (4968049721/10000000000 : ℝ)*x 1 + (3166644447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19668091/1000000000 : ℝ)^85 ≤ (790884139399/100000000000000 : ℝ)^69 := by
    have hnat : (19668091 : ℕ)^85*100000000000000^69 ≤ 790884139399^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19668091 1000000000 790884139399 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4968049721/10000000000 : ℝ)^85 ≤ (528015058171/1250000000000 : ℝ)^69 := by
    have hnat : (4968049721 : ℕ)^85*1250000000000^69 ≤ 528015058171^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4968049721 10000000000 528015058171 1250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3166644447/5000000000 : ℝ)^85 ≤ (56967911192251/100000000000000 : ℝ)^69 := by
    have hnat : (3166644447 : ℕ)^85*100000000000000^69 ≤ 56967911192251^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3166644447 5000000000 56967911192251 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19668091/1000000000 : ℝ), (4968049721/10000000000 : ℝ), (3166644447/5000000000 : ℝ)] ![(790884139399/100000000000000 : ℝ), (528015058171/1250000000000 : ℝ), (56967911192251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19668091/1000000000 : ℝ)|^85 ≤ (790884139399/100000000000000 : ℝ)^69
        have hw : |(-19668091/1000000000 : ℝ)|=(19668091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4968049721/10000000000 : ℝ)|^85 ≤ (528015058171/1250000000000 : ℝ)^69
        have hw : |(4968049721/10000000000 : ℝ)|=(4968049721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3166644447/5000000000 : ℝ)|^85 ≤ (56967911192251/100000000000000 : ℝ)^69
        have hw : |(3166644447/5000000000 : ℝ)|=(3166644447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2309525613/5000000000 : ℝ)*x 0 + (-98886873/1250000000 : ℝ)*x 1 + (791922731/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2309525613/5000000000 : ℝ)^85 ≤ (19308028006023/50000000000000 : ℝ)^69 := by
    have hnat : (2309525613 : ℕ)^85*50000000000000^69 ≤ 19308028006023^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309525613 5000000000 19308028006023 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98886873/1250000000 : ℝ)^85 ≤ (4392840298603/100000000000000 : ℝ)^69 := by
    have hnat : (98886873 : ℕ)^85*100000000000000^69 ≤ 4392840298603^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98886873 1250000000 4392840298603 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791922731/1250000000 : ℝ)^85 ≤ (2849555183513/5000000000000 : ℝ)^69 := by
    have hnat : (791922731 : ℕ)^85*5000000000000^69 ≤ 2849555183513^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791922731 1250000000 2849555183513 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2309525613/5000000000 : ℝ), (-98886873/1250000000 : ℝ), (791922731/1250000000 : ℝ)] ![(19308028006023/50000000000000 : ℝ), (4392840298603/100000000000000 : ℝ), (2849555183513/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2309525613/5000000000 : ℝ)|^85 ≤ (19308028006023/50000000000000 : ℝ)^69
        have hw : |(2309525613/5000000000 : ℝ)|=(2309525613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98886873/1250000000 : ℝ)|^85 ≤ (4392840298603/100000000000000 : ℝ)^69
        have hw : |(-98886873/1250000000 : ℝ)|=(98886873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(791922731/1250000000 : ℝ)|^85 ≤ (2849555183513/5000000000000 : ℝ)^69
        have hw : |(791922731/1250000000 : ℝ)|=(791922731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6304252753/10000000000 : ℝ)*x 0 + (156788299/312500000 : ℝ)*x 1 + (-31298271/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6304252753/10000000000 : ℝ)^85 ≤ (14161584739549/25000000000000 : ℝ)^69 := by
    have hnat : (6304252753 : ℕ)^85*25000000000000^69 ≤ 14161584739549^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6304252753 10000000000 14161584739549 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156788299/312500000 : ℝ)^85 ≤ (1710274846133/4000000000000 : ℝ)^69 := by
    have hnat : (156788299 : ℕ)^85*4000000000000^69 ≤ 1710274846133^69*312500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156788299 312500000 1710274846133 4000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31298271/2000000000 : ℝ)^85 ≤ (119357975123/20000000000000 : ℝ)^69 := by
    have hnat : (31298271 : ℕ)^85*20000000000000^69 ≤ 119357975123^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31298271 2000000000 119357975123 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6304252753/10000000000 : ℝ), (156788299/312500000 : ℝ), (-31298271/2000000000 : ℝ)] ![(14161584739549/25000000000000 : ℝ), (1710274846133/4000000000000 : ℝ), (119357975123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6304252753/10000000000 : ℝ)|^85 ≤ (14161584739549/25000000000000 : ℝ)^69
        have hw : |(6304252753/10000000000 : ℝ)|=(6304252753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156788299/312500000 : ℝ)|^85 ≤ (1710274846133/4000000000000 : ℝ)^69
        have hw : |(156788299/312500000 : ℝ)|=(156788299/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31298271/2000000000 : ℝ)|^85 ≤ (119357975123/20000000000000 : ℝ)^69
        have hw : |(-31298271/2000000000 : ℝ)|=(31298271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1333962521/2000000000 : ℝ)*x 0 + (1774218803/5000000000 : ℝ)*x 1 + (1712527491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333962521/2000000000 : ℝ)^85 ≤ (6071952806993/10000000000000 : ℝ)^69 := by
    have hnat : (1333962521 : ℕ)^85*10000000000000^69 ≤ 6071952806993^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333962521 2000000000 6071952806993 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1774218803/5000000000 : ℝ)^85 ≤ (6976506057759/25000000000000 : ℝ)^69 := by
    have hnat : (1774218803 : ℕ)^85*25000000000000^69 ≤ 6976506057759^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774218803 5000000000 6976506057759 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1712527491/10000000000 : ℝ)^85 ≤ (5687223842219/50000000000000 : ℝ)^69 := by
    have hnat : (1712527491 : ℕ)^85*50000000000000^69 ≤ 5687223842219^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712527491 10000000000 5687223842219 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1333962521/2000000000 : ℝ), (1774218803/5000000000 : ℝ), (1712527491/10000000000 : ℝ)] ![(6071952806993/10000000000000 : ℝ), (6976506057759/25000000000000 : ℝ), (5687223842219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1333962521/2000000000 : ℝ)|^85 ≤ (6071952806993/10000000000000 : ℝ)^69
        have hw : |(1333962521/2000000000 : ℝ)|=(1333962521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1774218803/5000000000 : ℝ)|^85 ≤ (6976506057759/25000000000000 : ℝ)^69
        have hw : |(1774218803/5000000000 : ℝ)|=(1774218803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1712527491/10000000000 : ℝ)|^85 ≤ (5687223842219/50000000000000 : ℝ)^69
        have hw : |(1712527491/10000000000 : ℝ)|=(1712527491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-152598917/10000000000 : ℝ)*x 0 + (5992925219/10000000000 : ℝ)*x 1 + (5342903729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (152598917/10000000000 : ℝ)^85 ≤ (578556784689/100000000000000 : ℝ)^69 := by
    have hnat : (152598917 : ℕ)^85*100000000000000^69 ≤ 578556784689^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152598917 10000000000 578556784689 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5992925219/10000000000 : ℝ)^85 ≤ (53220243184877/100000000000000 : ℝ)^69 := by
    have hnat : (5992925219 : ℕ)^85*100000000000000^69 ≤ 53220243184877^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5992925219 10000000000 53220243184877 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5342903729/10000000000 : ℝ)^85 ≤ (46201200014803/100000000000000 : ℝ)^69 := by
    have hnat : (5342903729 : ℕ)^85*100000000000000^69 ≤ 46201200014803^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342903729 10000000000 46201200014803 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-152598917/10000000000 : ℝ), (5992925219/10000000000 : ℝ), (5342903729/10000000000 : ℝ)] ![(578556784689/100000000000000 : ℝ), (53220243184877/100000000000000 : ℝ), (46201200014803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-152598917/10000000000 : ℝ)|^85 ≤ (578556784689/100000000000000 : ℝ)^69
        have hw : |(-152598917/10000000000 : ℝ)|=(152598917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5992925219/10000000000 : ℝ)|^85 ≤ (53220243184877/100000000000000 : ℝ)^69
        have hw : |(5992925219/10000000000 : ℝ)|=(5992925219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5342903729/10000000000 : ℝ)|^85 ≤ (46201200014803/100000000000000 : ℝ)^69
        have hw : |(5342903729/10000000000 : ℝ)|=(5342903729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1267277003/2000000000 : ℝ)*x 0 + (-69669727/5000000000 : ℝ)*x 1 + (998176997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1267277003/2000000000 : ℝ)^85 ≤ (57002220611661/100000000000000 : ℝ)^69 := by
    have hnat : (1267277003 : ℕ)^85*100000000000000^69 ≤ 57002220611661^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267277003 2000000000 57002220611661 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69669727/5000000000 : ℝ)^85 ≤ (129316661799/25000000000000 : ℝ)^69 := by
    have hnat : (69669727 : ℕ)^85*25000000000000^69 ≤ 129316661799^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69669727 5000000000 129316661799 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998176997/2000000000 : ℝ)^85 ≤ (42480512723347/100000000000000 : ℝ)^69 := by
    have hnat : (998176997 : ℕ)^85*100000000000000^69 ≤ 42480512723347^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998176997 2000000000 42480512723347 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1267277003/2000000000 : ℝ), (-69669727/5000000000 : ℝ), (998176997/2000000000 : ℝ)] ![(57002220611661/100000000000000 : ℝ), (129316661799/25000000000000 : ℝ), (42480512723347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1267277003/2000000000 : ℝ)|^85 ≤ (57002220611661/100000000000000 : ℝ)^69
        have hw : |(1267277003/2000000000 : ℝ)|=(1267277003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69669727/5000000000 : ℝ)|^85 ≤ (129316661799/25000000000000 : ℝ)^69
        have hw : |(-69669727/5000000000 : ℝ)|=(69669727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(998176997/2000000000 : ℝ)|^85 ≤ (42480512723347/100000000000000 : ℝ)^69
        have hw : |(998176997/2000000000 : ℝ)|=(998176997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4560667027/10000000000 : ℝ)*x 0 + (1279272467/2000000000 : ℝ)*x 1 + (-9749369/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4560667027/10000000000 : ℝ)^85 ≤ (4751956894623/12500000000000 : ℝ)^69 := by
    have hnat : (4560667027 : ℕ)^85*12500000000000^69 ≤ 4751956894623^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4560667027 10000000000 4751956894623 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279272467/2000000000 : ℝ)^85 ≤ (57667619874381/100000000000000 : ℝ)^69 := by
    have hnat : (1279272467 : ℕ)^85*100000000000000^69 ≤ 57667619874381^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279272467 2000000000 57667619874381 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9749369/125000000 : ℝ)^85 ≤ (4316724955869/100000000000000 : ℝ)^69 := by
    have hnat : (9749369 : ℕ)^85*100000000000000^69 ≤ 4316724955869^69*125000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9749369 125000000 4316724955869 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4560667027/10000000000 : ℝ), (1279272467/2000000000 : ℝ), (-9749369/125000000 : ℝ)] ![(4751956894623/12500000000000 : ℝ), (57667619874381/100000000000000 : ℝ), (4316724955869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4560667027/10000000000 : ℝ)|^85 ≤ (4751956894623/12500000000000 : ℝ)^69
        have hw : |(4560667027/10000000000 : ℝ)|=(4560667027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1279272467/2000000000 : ℝ)|^85 ≤ (57667619874381/100000000000000 : ℝ)^69
        have hw : |(1279272467/2000000000 : ℝ)|=(1279272467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9749369/125000000 : ℝ)|^85 ≤ (4316724955869/100000000000000 : ℝ)^69
        have hw : |(-9749369/125000000 : ℝ)|=(9749369/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324063_s1_s1_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6863061571/10000000000 : ℝ)*x 0 + (1319653009/5000000000 : ℝ)*x 1 + (1227522329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6863061571/10000000000 : ℝ)^85 ≤ (31446984424943/50000000000000 : ℝ)^69 := by
    have hnat : (6863061571 : ℕ)^85*50000000000000^69 ≤ 31446984424943^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6863061571 10000000000 31446984424943 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319653009/5000000000 : ℝ)^85 ≤ (4844873609393/25000000000000 : ℝ)^69 := by
    have hnat : (1319653009 : ℕ)^85*25000000000000^69 ≤ 4844873609393^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319653009 5000000000 4844873609393 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1227522329/5000000000 : ℝ)^85 ≤ (17726536702703/100000000000000 : ℝ)^69 := by
    have hnat : (1227522329 : ℕ)^85*100000000000000^69 ≤ 17726536702703^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227522329 5000000000 17726536702703 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6863061571/10000000000 : ℝ), (1319653009/5000000000 : ℝ), (1227522329/5000000000 : ℝ)] ![(31446984424943/50000000000000 : ℝ), (4844873609393/25000000000000 : ℝ), (17726536702703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6863061571/10000000000 : ℝ)|^85 ≤ (31446984424943/50000000000000 : ℝ)^69
        have hw : |(6863061571/10000000000 : ℝ)|=(6863061571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319653009/5000000000 : ℝ)|^85 ≤ (4844873609393/25000000000000 : ℝ)^69
        have hw : |(1319653009/5000000000 : ℝ)|=(1319653009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1227522329/5000000000 : ℝ)|^85 ≤ (17726536702703/100000000000000 : ℝ)^69
        have hw : |(1227522329/5000000000 : ℝ)|=(1227522329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324063_s1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2133/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2133/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6807/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6807/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65767/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65767/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((421/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(421/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10707/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10707/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40951/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40951/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (2133/3125 : ℝ) ^ (21/4 : ℝ) ≤ (6733011893481039479/50000000000000000000 : ℝ) := by
    have hpowers : (2133/3125 : ℝ)^21 ≤ (6733011893481039479/50000000000000000000 : ℝ)^4 := by
      have hnat : (2133 : ℕ)^21*50000000000000000000^4 ≤ 6733011893481039479^4*3125^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2133 3125 6733011893481039479 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2133/3125 : ℝ)) (X := (6733011893481039479/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (56733011893481039479/50000000000000000000 : ℝ) ≤ (2560888348040143/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (56733011893481039479/50000000000000000000 : ℝ)^4 ≤ (2560888348040143/2500000000000000 : ℝ)^21 := by
      have hnat : (56733011893481039479 : ℕ)^4*2500000000000000^21 ≤ 2560888348040143^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56733011893481039479 50000000000000000000 2560888348040143 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2560888348040143/2500000000000000 : ℝ)) (X := (56733011893481039479/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (31733011893481039479/25000000000000000000 : ℝ) ≤ (5232363028454629/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (31733011893481039479/25000000000000000000 : ℝ)^4 ≤ (5232363028454629/5000000000000000 : ℝ)^21 := by
      have hnat : (31733011893481039479 : ℕ)^4*5000000000000000^21 ≤ 5232363028454629^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31733011893481039479 25000000000000000000 5232363028454629 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5232363028454629/5000000000000000 : ℝ)) (X := (31733011893481039479/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(20296116013381/568800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(110586332374343/3412800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (2133/3125 : ℝ)) (alpha := (20296116013381/568800000000000 : ℝ)) (beta := (110586332374343/3412800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2133/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(20296116013381/568800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(110586332374343/3412800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6807/10000 : ℝ) ^ (21/4 : ℝ) ≤ (663724264645964879/5000000000000000000 : ℝ) := by
    have hpowers : (6807/10000 : ℝ)^21 ≤ (663724264645964879/5000000000000000000 : ℝ)^4 := by
      have hnat : (6807 : ℕ)^21*5000000000000000000^4 ≤ 663724264645964879^4*10000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6807 10000 663724264645964879 5000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6807/10000 : ℝ)) (X := (663724264645964879/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (5663724264645964879/5000000000000000000 : ℝ) ≤ (10240257458178723/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (5663724264645964879/5000000000000000000 : ℝ)^4 ≤ (10240257458178723/10000000000000000 : ℝ)^21 := by
      have hnat : (5663724264645964879 : ℕ)^4*10000000000000000^21 ≤ 10240257458178723^21*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5663724264645964879 5000000000000000000 10240257458178723 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10240257458178723/10000000000000000 : ℝ)) (X := (5663724264645964879/5000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (3163724264645964879/2500000000000000000 : ℝ) ≤ (2091740606847293/2000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3163724264645964879/2500000000000000000 : ℝ)^4 ≤ (2091740606847293/2000000000000000 : ℝ)^21 := by
      have hnat : (3163724264645964879 : ℕ)^4*2000000000000000^21 ≤ 2091740606847293^21*2500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3163724264645964879 2500000000000000000 2091740606847293 2000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2091740606847293/2000000000000000 : ℝ)) (X := (3163724264645964879/2500000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(240257458178723/6807000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(109222788028871/3403500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (6807/10000 : ℝ)) (alpha := (240257458178723/6807000000000000 : ℝ)) (beta := (109222788028871/3403500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6807/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(240257458178723/6807000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(109222788028871/3403500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (65767/100000 : ℝ) ^ (21/4 : ℝ) ≤ (2770015346620845603/25000000000000000000 : ℝ) := by
    have hpowers : (65767/100000 : ℝ)^21 ≤ (2770015346620845603/25000000000000000000 : ℝ)^4 := by
      have hnat : (65767 : ℕ)^21*25000000000000000000^4 ≤ 2770015346620845603^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65767 100000 2770015346620845603 25000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65767/100000 : ℝ)) (X := (2770015346620845603/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (27770015346620845603/25000000000000000000 : ℝ) ≤ (5101085430245637/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (27770015346620845603/25000000000000000000 : ℝ)^4 ≤ (5101085430245637/5000000000000000 : ℝ)^21 := by
      have hnat : (27770015346620845603 : ℕ)^4*5000000000000000^21 ≤ 5101085430245637^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27770015346620845603 25000000000000000000 5101085430245637 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5101085430245637/5000000000000000 : ℝ)) (X := (27770015346620845603/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (15270015346620845603/12500000000000000000 : ℝ) ≤ (5194311575843073/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (15270015346620845603/12500000000000000000 : ℝ)^4 ≤ (5194311575843073/5000000000000000 : ℝ)^21 := by
      have hnat : (15270015346620845603 : ℕ)^4*5000000000000000^21 ≤ 5194311575843073^21*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15270015346620845603 12500000000000000000 5194311575843073 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5194311575843073/5000000000000000 : ℝ)) (X := (15270015346620845603/12500000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(101085430245637/3288350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(23306536399359/822087500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (65767/100000 : ℝ)) (alpha := (101085430245637/3288350000000000 : ℝ)) (beta := (23306536399359/822087500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (65767/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(101085430245637/3288350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(23306536399359/822087500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-948471021/10000000000 : ℝ)*X 0 0+(5414213833/10000000000 : ℝ)*X 0 1+(1367177593/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2706998647/5000000000 : ℝ)*X 1 0+(-94570427/1000000000 : ℝ)*X 1 1+(5470768749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2722019987/5000000000 : ℝ)*X 2 0+(1092513871/2000000000 : ℝ)*X 2 1+(-182566577/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4160936417/10000000000 : ℝ)*X 0 0+(1028223813/2500000000 : ℝ)*X 0 1+(4023228187/10000000000 : ℝ)*X 0 2+(4160936417/10000000000 : ℝ)*X 1 0+(1028223813/2500000000 : ℝ)*X 1 1+(4023228187/10000000000 : ℝ)*X 1 2+(4160936417/10000000000 : ℝ)*X 2 0+(1028223813/2500000000 : ℝ)*X 2 1+(4023228187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-790684007/10000000000 : ℝ)*X 0 0+(2313858231/5000000000 : ℝ)*X 0 1+(632757959/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2487034809/5000000000 : ℝ)*X 1 0+(-38408237/2000000000 : ℝ)*X 1 1+(3164832981/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4719765747/10000000000 : ℝ)*X 2 0+(263564913/400000000 : ℝ)*X 2 1+(-141726751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1124702471/2500000000 : ℝ)*X 0 0+(582171341/1000000000 : ℝ)*X 0 1+(84957191/500000000 : ℝ)*X 0 2+(1124702471/2500000000 : ℝ)*X 1 0+(582171341/1000000000 : ℝ)*X 1 1+(84957191/500000000 : ℝ)*X 1 2+(1124702471/2500000000 : ℝ)*X 2 0+(582171341/1000000000 : ℝ)*X 2 1+(84957191/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-19668091/1000000000 : ℝ)*X 0 0+(4968049721/10000000000 : ℝ)*X 0 1+(3166644447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2309525613/5000000000 : ℝ)*X 1 0+(-98886873/1250000000 : ℝ)*X 1 1+(791922731/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6304252753/10000000000 : ℝ)*X 2 0+(156788299/312500000 : ℝ)*X 2 1+(-31298271/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1333962521/2000000000 : ℝ)*X 0 0+(1774218803/5000000000 : ℝ)*X 0 1+(1712527491/10000000000 : ℝ)*X 0 2+(1333962521/2000000000 : ℝ)*X 1 0+(1774218803/5000000000 : ℝ)*X 1 1+(1712527491/10000000000 : ℝ)*X 1 2+(1333962521/2000000000 : ℝ)*X 2 0+(1774218803/5000000000 : ℝ)*X 2 1+(1712527491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-152598917/10000000000 : ℝ)*X 0 0+(5992925219/10000000000 : ℝ)*X 0 1+(5342903729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1267277003/2000000000 : ℝ)*X 1 0+(-69669727/5000000000 : ℝ)*X 1 1+(998176997/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4560667027/10000000000 : ℝ)*X 2 0+(1279272467/2000000000 : ℝ)*X 2 1+(-9749369/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6863061571/10000000000 : ℝ)*X 0 0+(1319653009/5000000000 : ℝ)*X 0 1+(1227522329/5000000000 : ℝ)*X 0 2+(6863061571/10000000000 : ℝ)*X 1 0+(1319653009/5000000000 : ℝ)*X 1 1+(1227522329/5000000000 : ℝ)*X 1 2+(6863061571/10000000000 : ℝ)*X 2 0+(1319653009/5000000000 : ℝ)*X 2 1+(1227522329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((421/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(421/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (518927732260408401204365864459/35366401551000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65041/7812500000 : ℝ)*(base23) + (17495690481/100000000000 : ℝ)*(base60) + (1026952183029/250000000000 : ℝ)*(major_s1_0) + (1026952183029/250000000000 : ℝ)*(major_s1_1) + (1026952183029/250000000000 : ℝ)*(major_s1_2) + (1608101/1000000000000 : ℝ)*(sp_s1_0) + (6608183/500000000000 : ℝ)*(sp_s1_6) + (3071941195947/500000000000 : ℝ)*(sp_s1_7) + (95997966483/15625000000 : ℝ)*(sp_s1_8) + (3071935954713/500000000000 : ℝ)*(sp_s1_9) + (207166615873/100000000000 : ℝ)*(sp_s1_13) + (24599083/500000000000 : ℝ)*(sp_s1_14) + (253373/4000000000 : ℝ)*(sp_s1_15) + (1655109/31250000000 : ℝ)*(sp_s1_23) + (258959921887/125000000000 : ℝ)*(f.failure) + (3071966599081/500000000000 : ℝ)*(f.sum) + (2450227706118693711/18653165375000000000000000000000 : ℝ)*base62 + (2756844323501111/3288350000000000000000000000 : ℝ)*base65 + (106856820959739/141812500000000000000000000 : ℝ)*base67 + (21496029122731/1644175000000000000000000000 : ℝ)*base69 + (762825688942446949/3117355800000000000000000000000 : ℝ)*base71 + (43243968843809/284400000000000000000000000 : ℝ)*base73 + (129553008852489/567250000000000000000000000 : ℝ)*base75 + (3455366873803/47400000000000000000000000 : ℝ)*base77 + (344080910963309233/3226518000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (2023/3125000000000000 : ℝ)*base86 + (2023/3125000000000000 : ℝ)*base88 + (2023/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10707/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10707/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17012742450106636112244173837/1632295456200000000000000000000000 : ℝ) := by norm_num
    linear_combination (17269642079/500000000000 : ℝ)*(base7) + (1013378644937/250000000000 : ℝ)*(major_s1_0) + (1013378644937/250000000000 : ℝ)*(major_s1_1) + (1013378644937/250000000000 : ℝ)*(major_s1_2) + (6526843/500000000000 : ℝ)*(sp_s1_0) + (2683371/250000000000 : ℝ)*(sp_s1_1) + (6682233/500000000000 : ℝ)*(sp_s1_2) + (10649/7812500000 : ℝ)*(sp_s1_7) + (19879217/250000000000 : ℝ)*(sp_s1_8) + (6043590887233/1000000000000 : ℝ)*(sp_s1_14) + (151087876341/25000000000 : ℝ)*(sp_s1_15) + (3021795969763/500000000000 : ℝ)*(sp_s1_16) + (129925612187/62500000000 : ℝ)*(sp_s1_20) + (26850399/1000000000000 : ℝ)*(sp_s1_27) + (2044297361233/1000000000000 : ℝ)*(f.failure) + (6043605303991/1000000000000 : ℝ)*(f.sum) + (775401615957953743/1748734253906250000000000000000 : ℝ)*base63 + (2292827314269913/3288350000000000000000000000 : ℝ)*base65 + (585892110757177/850875000000000000000000000 : ℝ)*base67 + (1446715802026061/3288350000000000000000000000 : ℝ)*base69 + (2475229310043408371/9352067400000000000000000000000 : ℝ)*base71 + (67771557204271/853200000000000000000000000 : ℝ)*base73 + (355229106832013/850875000000000000000000000 : ℝ)*base75 + (26616466136957/142200000000000000000000000 : ℝ)*base77 + (1855062429969192047/9679554000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (18957/25000000000000000 : ℝ)*base86 + (18957/25000000000000000 : ℝ)*base88 + (18957/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40951/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40951/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12030767285944378541701109/806629500000000000000000000000 : ℝ) := by norm_num
    linear_combination (60459385511/1000000000000 : ℝ)*(base7) + (196038131281/1000000000000 : ℝ)*(base40) + (2221/12500000000 : ℝ)*(base49) + (465475075051/125000000000 : ℝ)*(major_s1_0) + (465475075051/125000000000 : ℝ)*(major_s1_1) + (465475075051/125000000000 : ℝ)*(major_s1_2) + (116852253/1000000000000 : ℝ)*(sp_s1_2) + (391881/10000000000 : ℝ)*(sp_s1_8) + (230348313/1000000000000 : ℝ)*(sp_s1_9) + (378367/31250000000 : ℝ)*(sp_s1_20) + (5536108628421/1000000000000 : ℝ)*(sp_s1_21) + (17300217001/3125000000 : ℝ)*(sp_s1_22) + (1107152285571/200000000000 : ℝ)*(sp_s1_23) + (121153808447/62500000000 : ℝ)*(sp_s1_27) + (234751707173/125000000000 : ℝ)*(f.failure) + (5536108628421/1000000000000 : ℝ)*(f.sum) + (33583746141803421833/111918992250000000000000000000000 : ℝ)*base62 + (259969855924723/3288350000000000000000000000 : ℝ)*base65 + (30788170530391/1701750000000000000000000000 : ℝ)*base66 + (103215503731961/205521875000000000000000000 : ℝ)*base69 + (2343775057987040087/4676033700000000000000000000000 : ℝ)*base70 + (452689794801293/426600000000000000000000000 : ℝ)*base73 + (16311224338813/212718750000000000000000000 : ℝ)*base74 + (17034733584719/71100000000000000000000000 : ℝ)*base76 + (724240045526443981/4839777000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (2217/3125000000000000 : ℝ)*base86 + (2217/3125000000000000 : ℝ)*base88 + (2217/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2133/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2133/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6807/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6807/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65767/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65767/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((421/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(421/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10707/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10707/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40951/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40951/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c324063_s1 p hpa hpb X hX hprev0

#print axioms solution
