-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309063_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:05:25.905658+00:00
-- url     : https://prove2.me/submissions/91f48f68-fd06-4011-aec1-55b571049699

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
theorem collision_support_c309063_s5_s5_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-893912001/5000000000 : ℝ)*x 0 + (1071883759/2000000000 : ℝ)*x 1 + (671823281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893912001/5000000000 : ℝ)^35 ≤ (10734735797677/100000000000000 : ℝ)^27 := by
    have hnat : (893912001 : ℕ)^35*100000000000000^27 ≤ 10734735797677^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893912001 5000000000 10734735797677 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071883759/2000000000 : ℝ)^35 ≤ (22275439194191/50000000000000 : ℝ)^27 := by
    have hnat : (1071883759 : ℕ)^35*50000000000000^27 ≤ 22275439194191^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071883759 2000000000 22275439194191 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (671823281/1250000000 : ℝ)^35 ≤ (2794649112441/6250000000000 : ℝ)^27 := by
    have hnat : (671823281 : ℕ)^35*6250000000000^27 ≤ 2794649112441^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671823281 1250000000 2794649112441 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-893912001/5000000000 : ℝ), (1071883759/2000000000 : ℝ), (671823281/1250000000 : ℝ)] ![(10734735797677/100000000000000 : ℝ), (22275439194191/50000000000000 : ℝ), (2794649112441/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-893912001/5000000000 : ℝ)|^35 ≤ (10734735797677/100000000000000 : ℝ)^27
        have hw : |(-893912001/5000000000 : ℝ)|=(893912001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1071883759/2000000000 : ℝ)|^35 ≤ (22275439194191/50000000000000 : ℝ)^27
        have hw : |(1071883759/2000000000 : ℝ)|=(1071883759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(671823281/1250000000 : ℝ)|^35 ≤ (2794649112441/6250000000000 : ℝ)^27
        have hw : |(671823281/1250000000 : ℝ)|=(671823281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2680001453/5000000000 : ℝ)*x 0 + (-1792560827/10000000000 : ℝ)*x 1 + (5370582207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680001453/5000000000 : ℝ)^35 ≤ (22278586328357/50000000000000 : ℝ)^27 := by
    have hnat : (2680001453 : ℕ)^35*50000000000000^27 ≤ 22278586328357^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680001453 5000000000 22278586328357 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1792560827/10000000000 : ℝ)^35 ≤ (86172951949/800000000000 : ℝ)^27 := by
    have hnat : (1792560827 : ℕ)^35*800000000000^27 ≤ 86172951949^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792560827 10000000000 86172951949 800000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5370582207/10000000000 : ℝ)^35 ≤ (4467120833959/10000000000000 : ℝ)^27 := by
    have hnat : (5370582207 : ℕ)^35*10000000000000^27 ≤ 4467120833959^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370582207 10000000000 4467120833959 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680001453/5000000000 : ℝ), (-1792560827/10000000000 : ℝ), (5370582207/10000000000 : ℝ)] ![(22278586328357/50000000000000 : ℝ), (86172951949/800000000000 : ℝ), (4467120833959/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680001453/5000000000 : ℝ)|^35 ≤ (22278586328357/50000000000000 : ℝ)^27
        have hw : |(2680001453/5000000000 : ℝ)|=(2680001453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1792560827/10000000000 : ℝ)|^35 ≤ (86172951949/800000000000 : ℝ)^27
        have hw : |(-1792560827/10000000000 : ℝ)|=(1792560827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5370582207/10000000000 : ℝ)|^35 ≤ (4467120833959/10000000000000 : ℝ)^27
        have hw : |(5370582207/10000000000 : ℝ)|=(5370582207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (167873187/312500000 : ℝ)*x 0 + (1073743093/2000000000 : ℝ)*x 1 + (-355721327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167873187/312500000 : ℝ)^35 ≤ (44685870386059/100000000000000 : ℝ)^27 := by
    have hnat : (167873187 : ℕ)^35*100000000000000^27 ≤ 44685870386059^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167873187 312500000 44685870386059 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073743093/2000000000 : ℝ)^35 ≤ (44651081640927/100000000000000 : ℝ)^27 := by
    have hnat : (1073743093 : ℕ)^35*100000000000000^27 ≤ 44651081640927^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073743093 2000000000 44651081640927 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355721327/2000000000 : ℝ)^35 ≤ (1332880994311/12500000000000 : ℝ)^27 := by
    have hnat : (355721327 : ℕ)^35*12500000000000^27 ≤ 1332880994311^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355721327 2000000000 1332880994311 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167873187/312500000 : ℝ), (1073743093/2000000000 : ℝ), (-355721327/2000000000 : ℝ)] ![(44685870386059/100000000000000 : ℝ), (44651081640927/100000000000000 : ℝ), (1332880994311/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167873187/312500000 : ℝ)|^35 ≤ (44685870386059/100000000000000 : ℝ)^27
        have hw : |(167873187/312500000 : ℝ)|=(167873187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1073743093/2000000000 : ℝ)|^35 ≤ (44651081640927/100000000000000 : ℝ)^27
        have hw : |(1073743093/2000000000 : ℝ)|=(1073743093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355721327/2000000000 : ℝ)|^35 ≤ (1332880994311/12500000000000 : ℝ)^27
        have hw : |(-355721327/2000000000 : ℝ)|=(355721327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4288452597/10000000000 : ℝ)*x 0 + (4286435087/10000000000 : ℝ)*x 1 + (855928669/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288452597/10000000000 : ℝ)^35 ≤ (33369726537431/100000000000000 : ℝ)^27 := by
    have hnat : (4288452597 : ℕ)^35*100000000000000^27 ≤ 33369726537431^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288452597 10000000000 33369726537431 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4286435087/10000000000 : ℝ)^35 ≤ (6669875519997/20000000000000 : ℝ)^27 := by
    have hnat : (4286435087 : ℕ)^35*20000000000000^27 ≤ 6669875519997^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286435087 10000000000 6669875519997 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (855928669/2000000000 : ℝ)^35 ≤ (33280895834651/100000000000000 : ℝ)^27 := by
    have hnat : (855928669 : ℕ)^35*100000000000000^27 ≤ 33280895834651^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855928669 2000000000 33280895834651 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288452597/10000000000 : ℝ), (4286435087/10000000000 : ℝ), (855928669/2000000000 : ℝ)] ![(33369726537431/100000000000000 : ℝ), (6669875519997/20000000000000 : ℝ), (33280895834651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288452597/10000000000 : ℝ)|^35 ≤ (33369726537431/100000000000000 : ℝ)^27
        have hw : |(4288452597/10000000000 : ℝ)|=(4288452597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4286435087/10000000000 : ℝ)|^35 ≤ (6669875519997/20000000000000 : ℝ)^27
        have hw : |(4286435087/10000000000 : ℝ)|=(4286435087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(855928669/2000000000 : ℝ)|^35 ≤ (33280895834651/100000000000000 : ℝ)^27
        have hw : |(855928669/2000000000 : ℝ)|=(855928669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-168814841/1000000000 : ℝ)*x 0 + (4616301283/10000000000 : ℝ)*x 1 + (6156333129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168814841/1000000000 : ℝ)^35 ≤ (155709560691/1562500000000 : ℝ)^27 := by
    have hnat : (168814841 : ℕ)^35*1562500000000^27 ≤ 155709560691^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168814841 1000000000 155709560691 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4616301283/10000000000 : ℝ)^35 ≤ (36713496191159/100000000000000 : ℝ)^27 := by
    have hnat : (4616301283 : ℕ)^35*100000000000000^27 ≤ 36713496191159^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616301283 10000000000 36713496191159 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6156333129/10000000000 : ℝ)^35 ≤ (53321091905497/100000000000000 : ℝ)^27 := by
    have hnat : (6156333129 : ℕ)^35*100000000000000^27 ≤ 53321091905497^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6156333129 10000000000 53321091905497 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168814841/1000000000 : ℝ), (4616301283/10000000000 : ℝ), (6156333129/10000000000 : ℝ)] ![(155709560691/1562500000000 : ℝ), (36713496191159/100000000000000 : ℝ), (53321091905497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168814841/1000000000 : ℝ)|^35 ≤ (155709560691/1562500000000 : ℝ)^27
        have hw : |(-168814841/1000000000 : ℝ)|=(168814841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4616301283/10000000000 : ℝ)|^35 ≤ (36713496191159/100000000000000 : ℝ)^27
        have hw : |(4616301283/10000000000 : ℝ)|=(4616301283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6156333129/10000000000 : ℝ)|^35 ≤ (53321091905497/100000000000000 : ℝ)^27
        have hw : |(6156333129/10000000000 : ℝ)|=(6156333129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2521911291/5000000000 : ℝ)*x 0 + (-1073855869/10000000000 : ℝ)*x 1 + (3076151057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2521911291/5000000000 : ℝ)^35 ≤ (41180217100391/100000000000000 : ℝ)^27 := by
    have hnat : (2521911291 : ℕ)^35*100000000000000^27 ≤ 41180217100391^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2521911291 5000000000 41180217100391 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073855869/10000000000 : ℝ)^35 ≤ (554394460899/10000000000000 : ℝ)^27 := by
    have hnat : (1073855869 : ℕ)^35*10000000000000^27 ≤ 554394460899^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073855869 10000000000 554394460899 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3076151057/5000000000 : ℝ)^35 ≤ (53275838269437/100000000000000 : ℝ)^27 := by
    have hnat : (3076151057 : ℕ)^35*100000000000000^27 ≤ 53275838269437^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3076151057 5000000000 53275838269437 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2521911291/5000000000 : ℝ), (-1073855869/10000000000 : ℝ), (3076151057/5000000000 : ℝ)] ![(41180217100391/100000000000000 : ℝ), (554394460899/10000000000000 : ℝ), (53275838269437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2521911291/5000000000 : ℝ)|^35 ≤ (41180217100391/100000000000000 : ℝ)^27
        have hw : |(2521911291/5000000000 : ℝ)|=(2521911291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073855869/10000000000 : ℝ)|^35 ≤ (554394460899/10000000000000 : ℝ)^27
        have hw : |(-1073855869/10000000000 : ℝ)|=(1073855869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3076151057/5000000000 : ℝ)|^35 ≤ (53275838269437/100000000000000 : ℝ)^27
        have hw : |(3076151057/5000000000 : ℝ)|=(3076151057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4854687313/10000000000 : ℝ)*x 0 + (1268501633/2000000000 : ℝ)*x 1 + (-262680863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4854687313/10000000000 : ℝ)^35 ≤ (9797426535489/25000000000000 : ℝ)^27 := by
    have hnat : (4854687313 : ℕ)^35*25000000000000^27 ≤ 9797426535489^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4854687313 10000000000 9797426535489 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268501633/2000000000 : ℝ)^35 ≤ (55420662368337/100000000000000 : ℝ)^27 := by
    have hnat : (1268501633 : ℕ)^35*100000000000000^27 ≤ 55420662368337^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268501633 2000000000 55420662368337 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262680863/2500000000 : ℝ)^35 ≤ (5389631472901/100000000000000 : ℝ)^27 := by
    have hnat : (262680863 : ℕ)^35*100000000000000^27 ≤ 5389631472901^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262680863 2500000000 5389631472901 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4854687313/10000000000 : ℝ), (1268501633/2000000000 : ℝ), (-262680863/2500000000 : ℝ)] ![(9797426535489/25000000000000 : ℝ), (55420662368337/100000000000000 : ℝ), (5389631472901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4854687313/10000000000 : ℝ)|^35 ≤ (9797426535489/25000000000000 : ℝ)^27
        have hw : |(4854687313/10000000000 : ℝ)|=(4854687313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1268501633/2000000000 : ℝ)|^35 ≤ (55420662368337/100000000000000 : ℝ)^27
        have hw : |(1268501633/2000000000 : ℝ)|=(1268501633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262680863/2500000000 : ℝ)|^35 ≤ (5389631472901/100000000000000 : ℝ)^27
        have hw : |(-262680863/2500000000 : ℝ)|=(262680863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2240389419/5000000000 : ℝ)*x 0 + (2779374143/5000000000 : ℝ)*x 1 + (166250061/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240389419/5000000000 : ℝ)^35 ≤ (7064490412983/20000000000000 : ℝ)^27 := by
    have hnat : (2240389419 : ℕ)^35*20000000000000^27 ≤ 7064490412983^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240389419 5000000000 7064490412983 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779374143/5000000000 : ℝ)^35 ≤ (46710513401963/100000000000000 : ℝ)^27 := by
    have hnat : (2779374143 : ℕ)^35*100000000000000^27 ≤ 46710513401963^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779374143 5000000000 46710513401963 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166250061/625000000 : ℝ)^35 ≤ (2245879314921/12500000000000 : ℝ)^27 := by
    have hnat : (166250061 : ℕ)^35*12500000000000^27 ≤ 2245879314921^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166250061 625000000 2245879314921 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240389419/5000000000 : ℝ), (2779374143/5000000000 : ℝ), (166250061/625000000 : ℝ)] ![(7064490412983/20000000000000 : ℝ), (46710513401963/100000000000000 : ℝ), (2245879314921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240389419/5000000000 : ℝ)|^35 ≤ (7064490412983/20000000000000 : ℝ)^27
        have hw : |(2240389419/5000000000 : ℝ)|=(2240389419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2779374143/5000000000 : ℝ)|^35 ≤ (46710513401963/100000000000000 : ℝ)^27
        have hw : |(2779374143/5000000000 : ℝ)|=(2779374143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166250061/625000000 : ℝ)|^35 ≤ (2245879314921/12500000000000 : ℝ)^27
        have hw : |(166250061/625000000 : ℝ)|=(166250061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070346561/10000000000 : ℝ)*x 0 + (5052277581/10000000000 : ℝ)*x 1 + (6146418803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070346561/10000000000 : ℝ)^35 ≤ (5520470550523/100000000000000 : ℝ)^27 := by
    have hnat : (1070346561 : ℕ)^35*100000000000000^27 ≤ 5520470550523^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070346561 10000000000 5520470550523 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5052277581/10000000000 : ℝ)^35 ≤ (41269723578451/100000000000000 : ℝ)^27 := by
    have hnat : (5052277581 : ℕ)^35*100000000000000^27 ≤ 41269723578451^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5052277581 10000000000 41269723578451 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6146418803/10000000000 : ℝ)^35 ≤ (6651225731829/12500000000000 : ℝ)^27 := by
    have hnat : (6146418803 : ℕ)^35*12500000000000^27 ≤ 6651225731829^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6146418803 10000000000 6651225731829 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070346561/10000000000 : ℝ), (5052277581/10000000000 : ℝ), (6146418803/10000000000 : ℝ)] ![(5520470550523/100000000000000 : ℝ), (41269723578451/100000000000000 : ℝ), (6651225731829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070346561/10000000000 : ℝ)|^35 ≤ (5520470550523/100000000000000 : ℝ)^27
        have hw : |(-1070346561/10000000000 : ℝ)|=(1070346561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5052277581/10000000000 : ℝ)|^35 ≤ (41269723578451/100000000000000 : ℝ)^27
        have hw : |(5052277581/10000000000 : ℝ)|=(5052277581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6146418803/10000000000 : ℝ)|^35 ≤ (6651225731829/12500000000000 : ℝ)^27
        have hw : |(6146418803/10000000000 : ℝ)|=(6146418803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (144822399/312500000 : ℝ)*x 0 + (-1684317657/10000000000 : ℝ)*x 1 + (6142386441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144822399/312500000 : ℝ)^35 ≤ (36899333379877/100000000000000 : ℝ)^27 := by
    have hnat : (144822399 : ℕ)^35*100000000000000^27 ≤ 36899333379877^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144822399 312500000 36899333379877 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1684317657/10000000000 : ℝ)^35 ≤ (39744431523/400000000000 : ℝ)^27 := by
    have hnat : (1684317657 : ℕ)^35*400000000000^27 ≤ 39744431523^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684317657 10000000000 39744431523 400000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6142386441/10000000000 : ℝ)^35 ≤ (13291139679517/25000000000000 : ℝ)^27 := by
    have hnat : (6142386441 : ℕ)^35*25000000000000^27 ≤ 13291139679517^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6142386441 10000000000 13291139679517 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(144822399/312500000 : ℝ), (-1684317657/10000000000 : ℝ), (6142386441/10000000000 : ℝ)] ![(36899333379877/100000000000000 : ℝ), (39744431523/400000000000 : ℝ), (13291139679517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(144822399/312500000 : ℝ)|^35 ≤ (36899333379877/100000000000000 : ℝ)^27
        have hw : |(144822399/312500000 : ℝ)|=(144822399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1684317657/10000000000 : ℝ)|^35 ≤ (39744431523/400000000000 : ℝ)^27
        have hw : |(-1684317657/10000000000 : ℝ)|=(1684317657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6142386441/10000000000 : ℝ)|^35 ≤ (13291139679517/25000000000000 : ℝ)^27
        have hw : |(6142386441/10000000000 : ℝ)|=(6142386441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6143613349/10000000000 : ℝ)*x 0 + (5061369889/10000000000 : ℝ)*x 1 + (-212127621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6143613349/10000000000 : ℝ)^35 ≤ (13294581230561/25000000000000 : ℝ)^27 := by
    have hnat : (6143613349 : ℕ)^35*25000000000000^27 ≤ 13294581230561^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6143613349 10000000000 13294581230561 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5061369889/10000000000 : ℝ)^35 ≤ (41366026286667/100000000000000 : ℝ)^27 := by
    have hnat : (5061369889 : ℕ)^35*100000000000000^27 ≤ 41366026286667^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5061369889 10000000000 41366026286667 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212127621/2000000000 : ℝ)^35 ≤ (54556487787/1000000000000 : ℝ)^27 := by
    have hnat : (212127621 : ℕ)^35*1000000000000^27 ≤ 54556487787^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212127621 2000000000 54556487787 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6143613349/10000000000 : ℝ), (5061369889/10000000000 : ℝ), (-212127621/2000000000 : ℝ)] ![(13294581230561/25000000000000 : ℝ), (41366026286667/100000000000000 : ℝ), (54556487787/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6143613349/10000000000 : ℝ)|^35 ≤ (13294581230561/25000000000000 : ℝ)^27
        have hw : |(6143613349/10000000000 : ℝ)|=(6143613349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5061369889/10000000000 : ℝ)|^35 ≤ (41366026286667/100000000000000 : ℝ)^27
        have hw : |(5061369889/10000000000 : ℝ)|=(5061369889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212127621/2000000000 : ℝ)|^35 ≤ (54556487787/1000000000000 : ℝ)^27
        have hw : |(-212127621/2000000000 : ℝ)|=(212127621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5961630781/10000000000 : ℝ)*x 0 + (4021038993/10000000000 : ℝ)*x 1 + (53633291/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5961630781/10000000000 : ℝ)^35 ≤ (2557269999587/5000000000000 : ℝ)^27 := by
    have hnat : (5961630781 : ℕ)^35*5000000000000^27 ≤ 2557269999587^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5961630781 10000000000 2557269999587 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021038993/10000000000 : ℝ)^35 ≤ (30697653785443/100000000000000 : ℝ)^27 := by
    have hnat : (4021038993 : ℕ)^35*100000000000000^27 ≤ 30697653785443^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021038993 10000000000 30697653785443 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53633291/200000000 : ℝ)^35 ≤ (3631389240097/20000000000000 : ℝ)^27 := by
    have hnat : (53633291 : ℕ)^35*20000000000000^27 ≤ 3631389240097^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53633291 200000000 3631389240097 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5961630781/10000000000 : ℝ), (4021038993/10000000000 : ℝ), (53633291/200000000 : ℝ)] ![(2557269999587/5000000000000 : ℝ), (30697653785443/100000000000000 : ℝ), (3631389240097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5961630781/10000000000 : ℝ)|^35 ≤ (2557269999587/5000000000000 : ℝ)^27
        have hw : |(5961630781/10000000000 : ℝ)|=(5961630781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4021038993/10000000000 : ℝ)|^35 ≤ (30697653785443/100000000000000 : ℝ)^27
        have hw : |(4021038993/10000000000 : ℝ)|=(4021038993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53633291/200000000 : ℝ)|^35 ≤ (3631389240097/20000000000000 : ℝ)^27
        have hw : |(53633291/200000000 : ℝ)|=(53633291/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-63454471/625000000 : ℝ)*x 0 + (582221763/1000000000 : ℝ)*x 1 + (5423677211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63454471/625000000 : ℝ)^35 ≤ (5155089371411/100000000000000 : ℝ)^27 := by
    have hnat : (63454471 : ℕ)^35*100000000000000^27 ≤ 5155089371411^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63454471 625000000 5155089371411 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582221763/1000000000 : ℝ)^35 ≤ (24800190262567/50000000000000 : ℝ)^27 := by
    have hnat : (582221763 : ℕ)^35*50000000000000^27 ≤ 24800190262567^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582221763 1000000000 24800190262567 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423677211/10000000000 : ℝ)^35 ≤ (22622265045557/50000000000000 : ℝ)^27 := by
    have hnat : (5423677211 : ℕ)^35*50000000000000^27 ≤ 22622265045557^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423677211 10000000000 22622265045557 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63454471/625000000 : ℝ), (582221763/1000000000 : ℝ), (5423677211/10000000000 : ℝ)] ![(5155089371411/100000000000000 : ℝ), (24800190262567/50000000000000 : ℝ), (22622265045557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63454471/625000000 : ℝ)|^35 ≤ (5155089371411/100000000000000 : ℝ)^27
        have hw : |(-63454471/625000000 : ℝ)|=(63454471/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582221763/1000000000 : ℝ)|^35 ≤ (24800190262567/50000000000000 : ℝ)^27
        have hw : |(582221763/1000000000 : ℝ)|=(582221763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423677211/10000000000 : ℝ)|^35 ≤ (22622265045557/50000000000000 : ℝ)^27
        have hw : |(5423677211/10000000000 : ℝ)|=(5423677211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (48331093/78125000 : ℝ)*x 0 + (-505505547/5000000000 : ℝ)*x 1 + (1009407603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48331093/78125000 : ℝ)^35 ≤ (6707335533659/12500000000000 : ℝ)^27 := by
    have hnat : (48331093 : ℕ)^35*12500000000000^27 ≤ 6707335533659^27*78125000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48331093 78125000 6707335533659 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505505547/5000000000 : ℝ)^35 ≤ (5127064567521/100000000000000 : ℝ)^27 := by
    have hnat : (505505547 : ℕ)^35*100000000000000^27 ≤ 5127064567521^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505505547 5000000000 5127064567521 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009407603/2000000000 : ℝ)^35 ≤ (41214251146549/100000000000000 : ℝ)^27 := by
    have hnat : (1009407603 : ℕ)^35*100000000000000^27 ≤ 41214251146549^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009407603 2000000000 41214251146549 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48331093/78125000 : ℝ), (-505505547/5000000000 : ℝ), (1009407603/2000000000 : ℝ)] ![(6707335533659/12500000000000 : ℝ), (5127064567521/100000000000000 : ℝ), (41214251146549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48331093/78125000 : ℝ)|^35 ≤ (6707335533659/12500000000000 : ℝ)^27
        have hw : |(48331093/78125000 : ℝ)|=(48331093/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505505547/5000000000 : ℝ)|^35 ≤ (5127064567521/100000000000000 : ℝ)^27
        have hw : |(-505505547/5000000000 : ℝ)|=(505505547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009407603/2000000000 : ℝ)|^35 ≤ (41214251146549/100000000000000 : ℝ)^27
        have hw : |(1009407603/2000000000 : ℝ)|=(1009407603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2288955257/5000000000 : ℝ)*x 0 + (6203914771/10000000000 : ℝ)*x 1 + (-834942489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2288955257/5000000000 : ℝ)^35 ≤ (36318196715389/100000000000000 : ℝ)^27 := by
    have hnat : (2288955257 : ℕ)^35*100000000000000^27 ≤ 36318196715389^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288955257 5000000000 36318196715389 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6203914771/10000000000 : ℝ)^35 ≤ (13463980772481/25000000000000 : ℝ)^27 := by
    have hnat : (6203914771 : ℕ)^35*25000000000000^27 ≤ 13463980772481^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6203914771 10000000000 13463980772481 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834942489/5000000000 : ℝ)^35 ≤ (4912940090333/50000000000000 : ℝ)^27 := by
    have hnat : (834942489 : ℕ)^35*50000000000000^27 ≤ 4912940090333^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834942489 5000000000 4912940090333 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2288955257/5000000000 : ℝ), (6203914771/10000000000 : ℝ), (-834942489/5000000000 : ℝ)] ![(36318196715389/100000000000000 : ℝ), (13463980772481/25000000000000 : ℝ), (4912940090333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2288955257/5000000000 : ℝ)|^35 ≤ (36318196715389/100000000000000 : ℝ)^27
        have hw : |(2288955257/5000000000 : ℝ)|=(2288955257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6203914771/10000000000 : ℝ)|^35 ≤ (13463980772481/25000000000000 : ℝ)^27
        have hw : |(6203914771/10000000000 : ℝ)|=(6203914771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-834942489/5000000000 : ℝ)|^35 ≤ (4912940090333/50000000000000 : ℝ)^27
        have hw : |(-834942489/5000000000 : ℝ)|=(834942489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s5_s5_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6111764041/10000000000 : ℝ)*x 0 + (1682014181/5000000000 : ℝ)*x 1 + (127948241/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6111764041/10000000000 : ℝ)^35 ≤ (52821232218079/100000000000000 : ℝ)^27 := by
    have hnat : (6111764041 : ℕ)^35*100000000000000^27 ≤ 52821232218079^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6111764041 10000000000 52821232218079 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1682014181/5000000000 : ℝ)^35 ≤ (24359586667537/100000000000000 : ℝ)^27 := by
    have hnat : (1682014181 : ℕ)^35*100000000000000^27 ≤ 24359586667537^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682014181 5000000000 24359586667537 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127948241/400000000 : ℝ)^35 ≤ (22819181111861/100000000000000 : ℝ)^27 := by
    have hnat : (127948241 : ℕ)^35*100000000000000^27 ≤ 22819181111861^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127948241 400000000 22819181111861 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6111764041/10000000000 : ℝ), (1682014181/5000000000 : ℝ), (127948241/400000000 : ℝ)] ![(52821232218079/100000000000000 : ℝ), (24359586667537/100000000000000 : ℝ), (22819181111861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6111764041/10000000000 : ℝ)|^35 ≤ (52821232218079/100000000000000 : ℝ)^27
        have hw : |(6111764041/10000000000 : ℝ)|=(6111764041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1682014181/5000000000 : ℝ)|^35 ≤ (24359586667537/100000000000000 : ℝ)^27
        have hw : |(1682014181/5000000000 : ℝ)|=(1682014181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127948241/400000000 : ℝ)|^35 ≤ (22819181111861/100000000000000 : ℝ)^27
        have hw : |(127948241/400000000 : ℝ)|=(127948241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309063_s5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((1259/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1259/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40899/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40899/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9759/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9759/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30989/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30989/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15673/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15673/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29993/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (1259/3125 : ℝ) ^ (69/16 : ℝ) ≤ (1982988714593485091/100000000000000000000 : ℝ) := by
    have hpowers : (1259/3125 : ℝ)^69 ≤ (1982988714593485091/100000000000000000000 : ℝ)^16 := by
      have hnat : (1259 : ℕ)^69*100000000000000000000^16 ≤ 1982988714593485091^16*3125^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1259 3125 1982988714593485091 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1259/3125 : ℝ)) (X := (1982988714593485091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner0a : (101982988714593485091/100000000000000000000 : ℝ) ≤ (10045636190877891/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (101982988714593485091/100000000000000000000 : ℝ)^16 ≤ (10045636190877891/10000000000000000 : ℝ)^69 := by
      have hnat : (101982988714593485091 : ℕ)^16*10000000000000000^69 ≤ 10045636190877891^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101982988714593485091 100000000000000000000 10045636190877891 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045636190877891/10000000000000000 : ℝ)) (X := (101982988714593485091/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner0b : (51982988714593485091/50000000000000000000 : ℝ) ≤ (10090595789361087/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (51982988714593485091/50000000000000000000 : ℝ)^16 ≤ (10090595789361087/10000000000000000 : ℝ)^69 := by
      have hnat : (51982988714593485091 : ℕ)^16*10000000000000000^69 ≤ 10090595789361087^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51982988714593485091 50000000000000000000 10090595789361087 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10090595789361087/10000000000000000 : ℝ)) (X := (51982988714593485091/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(45636190877891/4028800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11239899620799/1007200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1259/3125 : ℝ)) (alpha := (45636190877891/4028800000000000 : ℝ)) (beta := (11239899620799/1007200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1259/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(45636190877891/4028800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11239899620799/1007200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (40899/100000 : ℝ) ^ (69/16 : ℝ) ≤ (528994287057967269/25000000000000000000 : ℝ) := by
    have hpowers : (40899/100000 : ℝ)^69 ≤ (528994287057967269/25000000000000000000 : ℝ)^16 := by
      have hnat : (40899 : ℕ)^69*25000000000000000000^16 ≤ 528994287057967269^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40899 100000 528994287057967269 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40899/100000 : ℝ)) (X := (528994287057967269/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner1a : (25528994287057967269/25000000000000000000 : ℝ) ≤ (502433614896997/500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25528994287057967269/25000000000000000000 : ℝ)^16 ≤ (502433614896997/500000000000000 : ℝ)^69 := by
      have hnat : (25528994287057967269 : ℕ)^16*500000000000000^69 ≤ 502433614896997^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25528994287057967269 25000000000000000000 502433614896997 500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502433614896997/500000000000000 : ℝ)) (X := (25528994287057967269/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner1b : (13028994287057967269/12500000000000000000 : ℝ) ≤ (631035997906957/625000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (13028994287057967269/12500000000000000000 : ℝ)^16 ≤ (631035997906957/625000000000000 : ℝ)^69 := by
      have hnat : (13028994287057967269 : ℕ)^16*625000000000000^69 ≤ 631035997906957^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13028994287057967269 12500000000000000000 631035997906957 625000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631035997906957/625000000000000 : ℝ)) (X := (13028994287057967269/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2433614896997/204495000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(11975917142843/1022475000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (40899/100000 : ℝ)) (alpha := (2433614896997/204495000000000 : ℝ)) (beta := (11975917142843/1022475000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (40899/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2433614896997/204495000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(11975917142843/1022475000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (9759/25000 : ℝ) ^ (69/16 : ℝ) ≤ (1730589827114111559/100000000000000000000 : ℝ) := by
    have hpowers : (9759/25000 : ℝ)^69 ≤ (1730589827114111559/100000000000000000000 : ℝ)^16 := by
      have hnat : (9759 : ℕ)^69*100000000000000000000^16 ≤ 1730589827114111559^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9759 25000 1730589827114111559 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9759/25000 : ℝ)) (X := (1730589827114111559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner2a : (101730589827114111559/100000000000000000000 : ℝ) ≤ (2007973117444817/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (101730589827114111559/100000000000000000000 : ℝ)^16 ≤ (2007973117444817/2000000000000000 : ℝ)^69 := by
      have hnat : (101730589827114111559 : ℕ)^16*2000000000000000^69 ≤ 2007973117444817^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101730589827114111559 100000000000000000000 2007973117444817 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2007973117444817/2000000000000000 : ℝ)) (X := (101730589827114111559/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner2b : (51730589827114111559/50000000000000000000 : ℝ) ≤ (10079213612899533/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (51730589827114111559/50000000000000000000 : ℝ)^16 ≤ (10079213612899533/10000000000000000 : ℝ)^69 := by
      have hnat : (51730589827114111559 : ℕ)^16*10000000000000000^69 ≤ 10079213612899533^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51730589827114111559 50000000000000000000 10079213612899533 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10079213612899533/10000000000000000 : ℝ)) (X := (51730589827114111559/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2657705814939/260240000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(4918503209431/487950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (9759/25000 : ℝ)) (alpha := (2657705814939/260240000000000 : ℝ)) (beta := (4918503209431/487950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9759/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2657705814939/260240000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(4918503209431/487950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-893912001/5000000000 : ℝ)*X 0 0+(1071883759/2000000000 : ℝ)*X 0 1+(671823281/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((2680001453/5000000000 : ℝ)*X 1 0+(-1792560827/10000000000 : ℝ)*X 1 1+(5370582207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((167873187/312500000 : ℝ)*X 2 0+(1073743093/2000000000 : ℝ)*X 2 1+(-355721327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((4288452597/10000000000 : ℝ)*X 0 0+(4286435087/10000000000 : ℝ)*X 0 1+(855928669/2000000000 : ℝ)*X 0 2+(4288452597/10000000000 : ℝ)*X 1 0+(4286435087/10000000000 : ℝ)*X 1 1+(855928669/2000000000 : ℝ)*X 1 2+(4288452597/10000000000 : ℝ)*X 2 0+(4286435087/10000000000 : ℝ)*X 2 1+(855928669/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-168814841/1000000000 : ℝ)*X 0 0+(4616301283/10000000000 : ℝ)*X 0 1+(6156333129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((2521911291/5000000000 : ℝ)*X 1 0+(-1073855869/10000000000 : ℝ)*X 1 1+(3076151057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((4854687313/10000000000 : ℝ)*X 2 0+(1268501633/2000000000 : ℝ)*X 2 1+(-262680863/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((2240389419/5000000000 : ℝ)*X 0 0+(2779374143/5000000000 : ℝ)*X 0 1+(166250061/625000000 : ℝ)*X 0 2+(2240389419/5000000000 : ℝ)*X 1 0+(2779374143/5000000000 : ℝ)*X 1 1+(166250061/625000000 : ℝ)*X 1 2+(2240389419/5000000000 : ℝ)*X 2 0+(2779374143/5000000000 : ℝ)*X 2 1+(166250061/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-1070346561/10000000000 : ℝ)*X 0 0+(5052277581/10000000000 : ℝ)*X 0 1+(6146418803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((144822399/312500000 : ℝ)*X 1 0+(-1684317657/10000000000 : ℝ)*X 1 1+(6142386441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((6143613349/10000000000 : ℝ)*X 2 0+(5061369889/10000000000 : ℝ)*X 2 1+(-212127621/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((5961630781/10000000000 : ℝ)*X 0 0+(4021038993/10000000000 : ℝ)*X 0 1+(53633291/200000000 : ℝ)*X 0 2+(5961630781/10000000000 : ℝ)*X 1 0+(4021038993/10000000000 : ℝ)*X 1 1+(53633291/200000000 : ℝ)*X 1 2+(5961630781/10000000000 : ℝ)*X 2 0+(4021038993/10000000000 : ℝ)*X 2 1+(53633291/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-63454471/625000000 : ℝ)*X 0 0+(582221763/1000000000 : ℝ)*X 0 1+(5423677211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((48331093/78125000 : ℝ)*X 1 0+(-505505547/5000000000 : ℝ)*X 1 1+(1009407603/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((2288955257/5000000000 : ℝ)*X 2 0+(6203914771/10000000000 : ℝ)*X 2 1+(-834942489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((6111764041/10000000000 : ℝ)*X 0 0+(1682014181/5000000000 : ℝ)*X 0 1+(127948241/400000000 : ℝ)*X 0 2+(6111764041/10000000000 : ℝ)*X 1 0+(1682014181/5000000000 : ℝ)*X 1 1+(127948241/400000000 : ℝ)*X 1 2+(6111764041/10000000000 : ℝ)*X 2 0+(1682014181/5000000000 : ℝ)*X 2 1+(127948241/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((30989/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30989/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (131788985359325496490576931523/17866982269120000000000000000000000 : ℝ) := by norm_num
    linear_combination (1078141/1000000000000 : ℝ)*(base50) + (132904312239/1000000000000 : ℝ)*(base60) + (4808691575313/1000000000000 : ℝ)*(major_s5_0) + (4808691575313/1000000000000 : ℝ)*(major_s5_1) + (4808691575313/1000000000000 : ℝ)*(major_s5_2) + (5510911/500000000000 : ℝ)*(sp_s5_0) + (10666887/1000000000000 : ℝ)*(sp_s5_6) + (3298851465161/500000000000 : ℝ)*(sp_s5_7) + (6597685670233/1000000000000 : ℝ)*(sp_s5_8) + (412355502429/62500000000 : ℝ)*(sp_s5_9) + (1509816382291/500000000000 : ℝ)*(sp_s5_13) + (233083/10000000000 : ℝ)*(sp_s5_14) + (51590211/1000000000000 : ℝ)*(sp_s5_15) + (2461079/50000000000 : ℝ)*(sp_s5_23) + (301964343147/100000000000 : ℝ)*(f.failure) + (1649434315111/250000000000 : ℝ)*(f.sum) + (237189151817200153/709570384000000000000000000000 : ℝ)*base62 + (41548838864499/40662500000000000000000000 : ℝ)*base65 + (444511356470641/681650000000000000000000000 : ℝ)*base67 + (9243808225091/260240000000000000000000000 : ℝ)*base69 + (2343898202359952579/2621137280000000000000000000000 : ℝ)*base71 + (395164835259887/1007200000000000000000000000 : ℝ)*base73 + (28238175186543/136330000000000000000000000 : ℝ)*base75 + (2159635747025203/4028800000000000000000000000 : ℝ)*base77 + (1648186281488682099/2746231520000000000000000000000 : ℝ)*base79 + (309/10000000000000000 : ℝ)*base87 + (309/10000000000000000 : ℝ)*base89 + (309/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15673/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15673/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17803454412614359313721161/1773925960000000000000000000000 : ℝ) := by norm_num
    linear_combination (105481/40000000000 : ℝ)*(base60) + (973741842979/200000000000 : ℝ)*(major_s5_0) + (973741842979/200000000000 : ℝ)*(major_s5_1) + (973741842979/200000000000 : ℝ)*(major_s5_2) + (20622433/1000000000000 : ℝ)*(sp_s5_0) + (12030431/1000000000000 : ℝ)*(sp_s5_1) + (28832757/500000000000 : ℝ)*(sp_s5_2) + (8041207/200000000000 : ℝ)*(sp_s5_7) + (14380439/500000000000 : ℝ)*(sp_s5_8) + (3340011214349/500000000000 : ℝ)*(sp_s5_14) + (104375663529/15625000000 : ℝ)*(sp_s5_15) + (6680025591651/1000000000000 : ℝ)*(sp_s5_16) + (152863107357/50000000000 : ℝ)*(sp_s5_20) + (69680081/1000000000000 : ℝ)*(sp_s5_27) + (3057331827221/1000000000000 : ℝ)*(f.failure) + (3340041628583/500000000000 : ℝ)*(f.sum) + (1685355633626934823/10643555760000000000000000000000 : ℝ)*base63 + (3438772437769/97590000000000000000000000 : ℝ)*base65 + (11434234355203/102247500000000000000000000 : ℝ)*base67 + (174987586713181/260240000000000000000000000 : ℝ)*base69 + (972259390167886729/7863411840000000000000000000000 : ℝ)*base70 + (132784168120701/201440000000000000000000000 : ℝ)*base73 + (142173971250433/204495000000000000000000000 : ℝ)*base75 + (492819619936873/805760000000000000000000000 : ℝ)*base77 + (108108370748163893/1647738912000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (37413/100000000000000000 : ℝ)*base86 + (37413/100000000000000000 : ℝ)*base88 + (37413/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29993/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (145777495536534275359580575421/8933491134560000000000000000000000 : ℝ) := by norm_num
    linear_combination (229897710609/1000000000000 : ℝ)*(base40) + (4397529/1000000000000 : ℝ)*(base50) + (2248457142137/500000000000 : ℝ)*(major_s5_0) + (2248457142137/500000000000 : ℝ)*(major_s5_1) + (2248457142137/500000000000 : ℝ)*(major_s5_2) + (148257717/1000000000000 : ℝ)*(sp_s5_0) + (13743683/125000000000 : ℝ)*(sp_s5_1) + (31134921/500000000000 : ℝ)*(sp_s5_2) + (37879863/1000000000000 : ℝ)*(sp_s5_9) + (13267193/100000000000 : ℝ)*(sp_s5_20) + (3084906823451/500000000000 : ℝ)*(sp_s5_21) + (1233970391031/200000000000 : ℝ)*(sp_s5_22) + (3084930877457/500000000000 : ℝ)*(sp_s5_23) + (282372855263/100000000000 : ℝ)*(sp_s5_27) + (2823861224559/1000000000000 : ℝ)*(f.failure) + (6169961904619/1000000000000 : ℝ)*(f.sum) + (2939882998373611823/5321777880000000000000000000000 : ℝ)*base62 + (226866595612781/487950000000000000000000000 : ℝ)*base64 + (54057502528387/255618750000000000000000000 : ℝ)*base66 + (3318368707173/5204800000000000000000000 : ℝ)*base68 + (540171290650158799/3931705920000000000000000000000 : ℝ)*base70 + (230769950026817/503600000000000000000000000 : ℝ)*base72 + (305026975766741/408990000000000000000000000 : ℝ)*base74 + (795022040890293/2014400000000000000000000000 : ℝ)*base76 + (185756986059599407/4119347280000000000000000000000 : ℝ)*base78 + (52927/100000000000000000 : ℝ)*base86 + (52927/100000000000000000 : ℝ)*base88 + (52927/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((1259/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1259/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40899/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40899/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9759/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9759/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30989/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30989/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15673/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15673/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29993/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309063_s5 p hpa hpb X hX hprev4

#print axioms solution
