-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301061_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:38:26.736344+00:00
-- url     : https://prove2.me/submissions/b9e5bbdb-3374-4323-b72f-131309279b85

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
theorem collision_support_c301061_s6_s6_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-29354539/156250000 : ℝ)*x 0 + (2340034467/5000000000 : ℝ)*x 1 + (308029481/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29354539/156250000 : ℝ)^65 ≤ (435318111131/4000000000000 : ℝ)^49 := by
    have hnat : (29354539 : ℕ)^65*4000000000000^49 ≤ 435318111131^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29354539 156250000 435318111131 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2340034467/5000000000 : ℝ)^65 ≤ (4565512416769/12500000000000 : ℝ)^49 := by
    have hnat : (2340034467 : ℕ)^65*12500000000000^49 ≤ 4565512416769^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340034467 5000000000 4565512416769 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (308029481/500000000 : ℝ)^65 ≤ (52592947868743/100000000000000 : ℝ)^49 := by
    have hnat : (308029481 : ℕ)^65*100000000000000^49 ≤ 52592947868743^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308029481 500000000 52592947868743 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29354539/156250000 : ℝ), (2340034467/5000000000 : ℝ), (308029481/500000000 : ℝ)] ![(435318111131/4000000000000 : ℝ), (4565512416769/12500000000000 : ℝ), (52592947868743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29354539/156250000 : ℝ)|^65 ≤ (435318111131/4000000000000 : ℝ)^49
        have hw : |(-29354539/156250000 : ℝ)|=(29354539/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2340034467/5000000000 : ℝ)|^65 ≤ (4565512416769/12500000000000 : ℝ)^49
        have hw : |(2340034467/5000000000 : ℝ)|=(2340034467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(308029481/500000000 : ℝ)|^65 ≤ (52592947868743/100000000000000 : ℝ)^49
        have hw : |(308029481/500000000 : ℝ)|=(308029481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (600671983/1250000000 : ℝ)*x 0 + (-1949637167/10000000000 : ℝ)*x 1 + (5996386753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600671983/1250000000 : ℝ)^65 ≤ (1891348711621/5000000000000 : ℝ)^49 := by
    have hnat : (600671983 : ℕ)^65*5000000000000^49 ≤ 1891348711621^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600671983 1250000000 1891348711621 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949637167/10000000000 : ℝ)^65 ≤ (11431467173151/100000000000000 : ℝ)^49 := by
    have hnat : (1949637167 : ℕ)^65*100000000000000^49 ≤ 11431467173151^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949637167 10000000000 11431467173151 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5996386753/10000000000 : ℝ)^65 ≤ (25370779292461/50000000000000 : ℝ)^49 := by
    have hnat : (5996386753 : ℕ)^65*50000000000000^49 ≤ 25370779292461^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996386753 10000000000 25370779292461 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(600671983/1250000000 : ℝ), (-1949637167/10000000000 : ℝ), (5996386753/10000000000 : ℝ)] ![(1891348711621/5000000000000 : ℝ), (11431467173151/100000000000000 : ℝ), (25370779292461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(600671983/1250000000 : ℝ)|^65 ≤ (1891348711621/5000000000000 : ℝ)^49
        have hw : |(600671983/1250000000 : ℝ)|=(600671983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1949637167/10000000000 : ℝ)|^65 ≤ (11431467173151/100000000000000 : ℝ)^49
        have hw : |(-1949637167/10000000000 : ℝ)|=(1949637167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5996386753/10000000000 : ℝ)|^65 ≤ (25370779292461/50000000000000 : ℝ)^49
        have hw : |(5996386753/10000000000 : ℝ)|=(5996386753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4897980257/10000000000 : ℝ)*x 0 + (1321269397/2000000000 : ℝ)*x 1 + (-799399483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4897980257/10000000000 : ℝ)^65 ≤ (38796996112607/100000000000000 : ℝ)^49 := by
    have hnat : (4897980257 : ℕ)^65*100000000000000^49 ≤ 38796996112607^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4897980257 10000000000 38796996112607 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1321269397/2000000000 : ℝ)^65 ≤ (57699660751649/100000000000000 : ℝ)^49 := by
    have hnat : (1321269397 : ℕ)^65*100000000000000^49 ≤ 57699660751649^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321269397 2000000000 57699660751649 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (799399483/10000000000 : ℝ)^65 ≤ (3503343127693/100000000000000 : ℝ)^49 := by
    have hnat : (799399483 : ℕ)^65*100000000000000^49 ≤ 3503343127693^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799399483 10000000000 3503343127693 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4897980257/10000000000 : ℝ), (1321269397/2000000000 : ℝ), (-799399483/10000000000 : ℝ)] ![(38796996112607/100000000000000 : ℝ), (57699660751649/100000000000000 : ℝ), (3503343127693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4897980257/10000000000 : ℝ)|^65 ≤ (38796996112607/100000000000000 : ℝ)^49
        have hw : |(4897980257/10000000000 : ℝ)|=(4897980257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1321269397/2000000000 : ℝ)|^65 ≤ (57699660751649/100000000000000 : ℝ)^49
        have hw : |(1321269397/2000000000 : ℝ)|=(1321269397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-799399483/10000000000 : ℝ)|^65 ≤ (3503343127693/100000000000000 : ℝ)^49
        have hw : |(-799399483/10000000000 : ℝ)|=(799399483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6318896627/10000000000 : ℝ)*x 0 + (2996344231/10000000000 : ℝ)*x 1 + (444769667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6318896627/10000000000 : ℝ)^65 ≤ (10878637662253/20000000000000 : ℝ)^49 := by
    have hnat : (6318896627 : ℕ)^65*20000000000000^49 ≤ 10878637662253^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6318896627 10000000000 10878637662253 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2996344231/10000000000 : ℝ)^65 ≤ (20215424912167/100000000000000 : ℝ)^49 := by
    have hnat : (2996344231 : ℕ)^65*100000000000000^49 ≤ 20215424912167^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996344231 10000000000 20215424912167 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444769667/1250000000 : ℝ)^65 ≤ (12695693383209/50000000000000 : ℝ)^49 := by
    have hnat : (444769667 : ℕ)^65*50000000000000^49 ≤ 12695693383209^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444769667 1250000000 12695693383209 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6318896627/10000000000 : ℝ), (2996344231/10000000000 : ℝ), (444769667/1250000000 : ℝ)] ![(10878637662253/20000000000000 : ℝ), (20215424912167/100000000000000 : ℝ), (12695693383209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6318896627/10000000000 : ℝ)|^65 ≤ (10878637662253/20000000000000 : ℝ)^49
        have hw : |(6318896627/10000000000 : ℝ)|=(6318896627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2996344231/10000000000 : ℝ)|^65 ≤ (20215424912167/100000000000000 : ℝ)^49
        have hw : |(2996344231/10000000000 : ℝ)|=(2996344231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(444769667/1250000000 : ℝ)|^65 ≤ (12695693383209/50000000000000 : ℝ)^49
        have hw : |(444769667/1250000000 : ℝ)|=(444769667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1653324449/10000000000 : ℝ)*x 0 + (3758047007/10000000000 : ℝ)*x 1 + (7102151483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1653324449/10000000000 : ℝ)^65 ≤ (9186034580629/100000000000000 : ℝ)^49 := by
    have hnat : (1653324449 : ℕ)^65*100000000000000^49 ≤ 9186034580629^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653324449 10000000000 9186034580629 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3758047007/10000000000 : ℝ)^65 ≤ (13650368074227/50000000000000 : ℝ)^49 := by
    have hnat : (3758047007 : ℕ)^65*50000000000000^49 ≤ 13650368074227^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758047007 10000000000 13650368074227 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7102151483/10000000000 : ℝ)^65 ≤ (63513229250121/100000000000000 : ℝ)^49 := by
    have hnat : (7102151483 : ℕ)^65*100000000000000^49 ≤ 63513229250121^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7102151483 10000000000 63513229250121 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1653324449/10000000000 : ℝ), (3758047007/10000000000 : ℝ), (7102151483/10000000000 : ℝ)] ![(9186034580629/100000000000000 : ℝ), (13650368074227/50000000000000 : ℝ), (63513229250121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1653324449/10000000000 : ℝ)|^65 ≤ (9186034580629/100000000000000 : ℝ)^49
        have hw : |(-1653324449/10000000000 : ℝ)|=(1653324449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3758047007/10000000000 : ℝ)|^65 ≤ (13650368074227/50000000000000 : ℝ)^49
        have hw : |(3758047007/10000000000 : ℝ)|=(3758047007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7102151483/10000000000 : ℝ)|^65 ≤ (63513229250121/100000000000000 : ℝ)^49
        have hw : |(7102151483/10000000000 : ℝ)|=(7102151483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (821057389/2000000000 : ℝ)*x 0 + (-1249282557/10000000000 : ℝ)*x 1 + (3528126841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821057389/2000000000 : ℝ)^65 ≤ (7674115814313/25000000000000 : ℝ)^49 := by
    have hnat : (821057389 : ℕ)^65*25000000000000^49 ≤ 7674115814313^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821057389 2000000000 7674115814313 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249282557/10000000000 : ℝ)^65 ≤ (1583553507051/25000000000000 : ℝ)^49 := by
    have hnat : (1249282557 : ℕ)^65*25000000000000^49 ≤ 1583553507051^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249282557 10000000000 1583553507051 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3528126841/5000000000 : ℝ)^65 ≤ (15742330676907/25000000000000 : ℝ)^49 := by
    have hnat : (3528126841 : ℕ)^65*25000000000000^49 ≤ 15742330676907^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3528126841 5000000000 15742330676907 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(821057389/2000000000 : ℝ), (-1249282557/10000000000 : ℝ), (3528126841/5000000000 : ℝ)] ![(7674115814313/25000000000000 : ℝ), (1583553507051/25000000000000 : ℝ), (15742330676907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(821057389/2000000000 : ℝ)|^65 ≤ (7674115814313/25000000000000 : ℝ)^49
        have hw : |(821057389/2000000000 : ℝ)|=(821057389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1249282557/10000000000 : ℝ)|^65 ≤ (1583553507051/25000000000000 : ℝ)^49
        have hw : |(-1249282557/10000000000 : ℝ)|=(1249282557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3528126841/5000000000 : ℝ)|^65 ≤ (15742330676907/25000000000000 : ℝ)^49
        have hw : |(3528126841/5000000000 : ℝ)|=(3528126841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (131295953/312500000 : ℝ)*x 0 + (187642703/250000000 : ℝ)*x 1 + (-2224039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131295953/312500000 : ℝ)^65 ≤ (7913531376791/25000000000000 : ℝ)^49 := by
    have hnat : (131295953 : ℕ)^65*25000000000000^49 ≤ 7913531376791^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131295953 312500000 7913531376791 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187642703/250000000 : ℝ)^65 ≤ (68344447647403/100000000000000 : ℝ)^49 := by
    have hnat : (187642703 : ℕ)^65*100000000000000^49 ≤ 68344447647403^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187642703 250000000 68344447647403 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2224039/10000000000 : ℝ)^65 ≤ (1426831109/100000000000000 : ℝ)^49 := by
    have hnat : (2224039 : ℕ)^65*100000000000000^49 ≤ 1426831109^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224039 10000000000 1426831109 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131295953/312500000 : ℝ), (187642703/250000000 : ℝ), (-2224039/10000000000 : ℝ)] ![(7913531376791/25000000000000 : ℝ), (68344447647403/100000000000000 : ℝ), (1426831109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131295953/312500000 : ℝ)|^65 ≤ (7913531376791/25000000000000 : ℝ)^49
        have hw : |(131295953/312500000 : ℝ)|=(131295953/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(187642703/250000000 : ℝ)|^65 ≤ (68344447647403/100000000000000 : ℝ)^49
        have hw : |(187642703/250000000 : ℝ)|=(187642703/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2224039/10000000000 : ℝ)|^65 ≤ (1426831109/100000000000000 : ℝ)^49
        have hw : |(-2224039/10000000000 : ℝ)|=(2224039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5523332683/10000000000 : ℝ)*x 0 + (41429137/80000000 : ℝ)*x 1 + (132112903/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5523332683/10000000000 : ℝ)^65 ≤ (9100222251401/20000000000000 : ℝ)^49 := by
    have hnat : (5523332683 : ℕ)^65*20000000000000^49 ≤ 9100222251401^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523332683 10000000000 9100222251401 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41429137/80000000 : ℝ)^65 ≤ (41773286297769/100000000000000 : ℝ)^49 := by
    have hnat : (41429137 : ℕ)^65*100000000000000^49 ≤ 41773286297769^49*80000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41429137 80000000 41773286297769 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132112903/625000000 : ℝ)^65 ≤ (2545120485263/20000000000000 : ℝ)^49 := by
    have hnat : (132112903 : ℕ)^65*20000000000000^49 ≤ 2545120485263^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132112903 625000000 2545120485263 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5523332683/10000000000 : ℝ), (41429137/80000000 : ℝ), (132112903/625000000 : ℝ)] ![(9100222251401/20000000000000 : ℝ), (41773286297769/100000000000000 : ℝ), (2545120485263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5523332683/10000000000 : ℝ)|^65 ≤ (9100222251401/20000000000000 : ℝ)^49
        have hw : |(5523332683/10000000000 : ℝ)|=(5523332683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41429137/80000000 : ℝ)|^65 ≤ (41773286297769/100000000000000 : ℝ)^49
        have hw : |(41429137/80000000 : ℝ)|=(41429137/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132112903/625000000 : ℝ)|^65 ≤ (2545120485263/20000000000000 : ℝ)^49
        have hw : |(132112903/625000000 : ℝ)|=(132112903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-770901997/10000000000 : ℝ)*x 0 + (3970708413/10000000000 : ℝ)*x 1 + (7418457669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (770901997/10000000000 : ℝ)^65 ≤ (1669322829591/50000000000000 : ℝ)^49 := by
    have hnat : (770901997 : ℕ)^65*50000000000000^49 ≤ 1669322829591^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770901997 10000000000 1669322829591 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3970708413/10000000000 : ℝ)^65 ≤ (7342198570447/25000000000000 : ℝ)^49 := by
    have hnat : (3970708413 : ℕ)^65*25000000000000^49 ≤ 7342198570447^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3970708413 10000000000 7342198570447 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7418457669/10000000000 : ℝ)^65 ≤ (2691702402079/4000000000000 : ℝ)^49 := by
    have hnat : (7418457669 : ℕ)^65*4000000000000^49 ≤ 2691702402079^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7418457669 10000000000 2691702402079 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-770901997/10000000000 : ℝ), (3970708413/10000000000 : ℝ), (7418457669/10000000000 : ℝ)] ![(1669322829591/50000000000000 : ℝ), (7342198570447/25000000000000 : ℝ), (2691702402079/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-770901997/10000000000 : ℝ)|^65 ≤ (1669322829591/50000000000000 : ℝ)^49
        have hw : |(-770901997/10000000000 : ℝ)|=(770901997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3970708413/10000000000 : ℝ)|^65 ≤ (7342198570447/25000000000000 : ℝ)^49
        have hw : |(3970708413/10000000000 : ℝ)|=(3970708413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7418457669/10000000000 : ℝ)|^65 ≤ (2691702402079/4000000000000 : ℝ)^49
        have hw : |(7418457669/10000000000 : ℝ)|=(7418457669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (710791527/2000000000 : ℝ)*x 0 + (-11567939/78125000 : ℝ)*x 1 + (921274333/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (710791527/2000000000 : ℝ)^65 ≤ (25351638956777/100000000000000 : ℝ)^49 := by
    have hnat : (710791527 : ℕ)^65*100000000000000^49 ≤ 25351638956777^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710791527 2000000000 25351638956777 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11567939/78125000 : ℝ)^65 ≤ (7935927678409/100000000000000 : ℝ)^49 := by
    have hnat : (11567939 : ℕ)^65*100000000000000^49 ≤ 7935927678409^49*78125000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11567939 78125000 7935927678409 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921274333/1250000000 : ℝ)^65 ≤ (33356216680897/50000000000000 : ℝ)^49 := by
    have hnat : (921274333 : ℕ)^65*50000000000000^49 ≤ 33356216680897^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921274333 1250000000 33356216680897 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(710791527/2000000000 : ℝ), (-11567939/78125000 : ℝ), (921274333/1250000000 : ℝ)] ![(25351638956777/100000000000000 : ℝ), (7935927678409/100000000000000 : ℝ), (33356216680897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(710791527/2000000000 : ℝ)|^65 ≤ (25351638956777/100000000000000 : ℝ)^49
        have hw : |(710791527/2000000000 : ℝ)|=(710791527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11567939/78125000 : ℝ)|^65 ≤ (7935927678409/100000000000000 : ℝ)^49
        have hw : |(-11567939/78125000 : ℝ)|=(11567939/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921274333/1250000000 : ℝ)|^65 ≤ (33356216680897/50000000000000 : ℝ)^49
        have hw : |(921274333/1250000000 : ℝ)|=(921274333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6630423709/10000000000 : ℝ)*x 0 + (5193078731/10000000000 : ℝ)*x 1 + (-26003989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6630423709/10000000000 : ℝ)^65 ≤ (28989388357417/50000000000000 : ℝ)^49 := by
    have hnat : (6630423709 : ℕ)^65*50000000000000^49 ≤ 28989388357417^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6630423709 10000000000 28989388357417 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5193078731/10000000000 : ℝ)^65 ≤ (41927834023607/100000000000000 : ℝ)^49 := by
    have hnat : (5193078731 : ℕ)^65*100000000000000^49 ≤ 41927834023607^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193078731 10000000000 41927834023607 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26003989/5000000000 : ℝ)^65 ≤ (18677850449/20000000000000 : ℝ)^49 := by
    have hnat : (26003989 : ℕ)^65*20000000000000^49 ≤ 18677850449^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26003989 5000000000 18677850449 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6630423709/10000000000 : ℝ), (5193078731/10000000000 : ℝ), (-26003989/5000000000 : ℝ)] ![(28989388357417/50000000000000 : ℝ), (41927834023607/100000000000000 : ℝ), (18677850449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6630423709/10000000000 : ℝ)|^65 ≤ (28989388357417/50000000000000 : ℝ)^49
        have hw : |(6630423709/10000000000 : ℝ)|=(6630423709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5193078731/10000000000 : ℝ)|^65 ≤ (41927834023607/100000000000000 : ℝ)^49
        have hw : |(5193078731/10000000000 : ℝ)|=(5193078731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26003989/5000000000 : ℝ)|^65 ≤ (18677850449/20000000000000 : ℝ)^49
        have hw : |(-26003989/5000000000 : ℝ)|=(26003989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (158101669/200000000 : ℝ)*x 0 + (2465198633/10000000000 : ℝ)*x 1 + (958917577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158101669/200000000 : ℝ)^65 ≤ (9151237053519/12500000000000 : ℝ)^49 := by
    have hnat : (158101669 : ℕ)^65*12500000000000^49 ≤ 9151237053519^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158101669 200000000 9151237053519 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2465198633/10000000000 : ℝ)^65 ≤ (1560532984909/10000000000000 : ℝ)^49 := by
    have hnat : (2465198633 : ℕ)^65*10000000000000^49 ≤ 1560532984909^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465198633 10000000000 1560532984909 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958917577/5000000000 : ℝ)^65 ≤ (1118477370081/10000000000000 : ℝ)^49 := by
    have hnat : (958917577 : ℕ)^65*10000000000000^49 ≤ 1118477370081^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958917577 5000000000 1118477370081 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(158101669/200000000 : ℝ), (2465198633/10000000000 : ℝ), (958917577/5000000000 : ℝ)] ![(9151237053519/12500000000000 : ℝ), (1560532984909/10000000000000 : ℝ), (1118477370081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(158101669/200000000 : ℝ)|^65 ≤ (9151237053519/12500000000000 : ℝ)^49
        have hw : |(158101669/200000000 : ℝ)|=(158101669/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2465198633/10000000000 : ℝ)|^65 ≤ (1560532984909/10000000000000 : ℝ)^49
        have hw : |(2465198633/10000000000 : ℝ)|=(2465198633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958917577/5000000000 : ℝ)|^65 ≤ (1118477370081/10000000000000 : ℝ)^49
        have hw : |(958917577/5000000000 : ℝ)|=(958917577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-490922671/10000000000 : ℝ)*x 0 + (762105641/1250000000 : ℝ)*x 1 + (1398908747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490922671/10000000000 : ℝ)^65 ≤ (183480025071/10000000000000 : ℝ)^49 := by
    have hnat : (490922671 : ℕ)^65*10000000000000^49 ≤ 183480025071^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490922671 10000000000 183480025071 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (762105641/1250000000 : ℝ)^65 ≤ (10374457986383/20000000000000 : ℝ)^49 := by
    have hnat : (762105641 : ℕ)^65*20000000000000^49 ≤ 10374457986383^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762105641 1250000000 10374457986383 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1398908747/2500000000 : ℝ)^65 ≤ (9258581959313/20000000000000 : ℝ)^49 := by
    have hnat : (1398908747 : ℕ)^65*20000000000000^49 ≤ 9258581959313^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398908747 2500000000 9258581959313 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490922671/10000000000 : ℝ), (762105641/1250000000 : ℝ), (1398908747/2500000000 : ℝ)] ![(183480025071/10000000000000 : ℝ), (10374457986383/20000000000000 : ℝ), (9258581959313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490922671/10000000000 : ℝ)|^65 ≤ (183480025071/10000000000000 : ℝ)^49
        have hw : |(-490922671/10000000000 : ℝ)|=(490922671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(762105641/1250000000 : ℝ)|^65 ≤ (10374457986383/20000000000000 : ℝ)^49
        have hw : |(762105641/1250000000 : ℝ)|=(762105641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1398908747/2500000000 : ℝ)|^65 ≤ (9258581959313/20000000000000 : ℝ)^49
        have hw : |(1398908747/2500000000 : ℝ)|=(1398908747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6536060587/10000000000 : ℝ)*x 0 + (-552903459/10000000000 : ℝ)*x 1 + (5102922487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6536060587/10000000000 : ℝ)^65 ≤ (88885544739/156250000000 : ℝ)^49 := by
    have hnat : (6536060587 : ℕ)^65*156250000000^49 ≤ 88885544739^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6536060587 10000000000 88885544739 156250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552903459/10000000000 : ℝ)^65 ≤ (214825492101/10000000000000 : ℝ)^49 := by
    have hnat : (552903459 : ℕ)^65*10000000000000^49 ≤ 214825492101^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552903459 10000000000 214825492101 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5102922487/10000000000 : ℝ)^65 ≤ (20482498215317/50000000000000 : ℝ)^49 := by
    have hnat : (5102922487 : ℕ)^65*50000000000000^49 ≤ 20482498215317^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5102922487 10000000000 20482498215317 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6536060587/10000000000 : ℝ), (-552903459/10000000000 : ℝ), (5102922487/10000000000 : ℝ)] ![(88885544739/156250000000 : ℝ), (214825492101/10000000000000 : ℝ), (20482498215317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6536060587/10000000000 : ℝ)|^65 ≤ (88885544739/156250000000 : ℝ)^49
        have hw : |(6536060587/10000000000 : ℝ)|=(6536060587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-552903459/10000000000 : ℝ)|^65 ≤ (214825492101/10000000000000 : ℝ)^49
        have hw : |(-552903459/10000000000 : ℝ)|=(552903459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5102922487/10000000000 : ℝ)|^65 ≤ (20482498215317/50000000000000 : ℝ)^49
        have hw : |(5102922487/10000000000 : ℝ)|=(5102922487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3804491939/10000000000 : ℝ)*x 0 + (7725562507/10000000000 : ℝ)*x 1 + (-4561889/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3804491939/10000000000 : ℝ)^65 ≤ (27749213756249/100000000000000 : ℝ)^49 := by
    have hnat : (3804491939 : ℕ)^65*100000000000000^49 ≤ 27749213756249^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3804491939 10000000000 27749213756249 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7725562507/10000000000 : ℝ)^65 ≤ (35506336569971/50000000000000 : ℝ)^49 := by
    have hnat : (7725562507 : ℕ)^65*50000000000000^49 ≤ 35506336569971^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7725562507 10000000000 35506336569971 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4561889/125000000 : ℝ)^65 ≤ (77382068511/6250000000000 : ℝ)^49 := by
    have hnat : (4561889 : ℕ)^65*6250000000000^49 ≤ 77382068511^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561889 125000000 77382068511 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3804491939/10000000000 : ℝ), (7725562507/10000000000 : ℝ), (-4561889/125000000 : ℝ)] ![(27749213756249/100000000000000 : ℝ), (35506336569971/50000000000000 : ℝ), (77382068511/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3804491939/10000000000 : ℝ)|^65 ≤ (27749213756249/100000000000000 : ℝ)^49
        have hw : |(3804491939/10000000000 : ℝ)|=(3804491939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7725562507/10000000000 : ℝ)|^65 ≤ (35506336569971/50000000000000 : ℝ)^49
        have hw : |(7725562507/10000000000 : ℝ)|=(7725562507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4561889/125000000 : ℝ)|^65 ≤ (77382068511/6250000000000 : ℝ)^49
        have hw : |(-4561889/125000000 : ℝ)|=(4561889/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s6_s6_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1649867113/2000000000 : ℝ)*x 0 + (1964793517/10000000000 : ℝ)*x 1 + (236439701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1649867113/2000000000 : ℝ)^65 ≤ (77468867160591/100000000000000 : ℝ)^49 := by
    have hnat : (1649867113 : ℕ)^65*100000000000000^49 ≤ 77468867160591^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649867113 2000000000 77468867160591 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964793517/10000000000 : ℝ)^65 ≤ (461980078027/4000000000000 : ℝ)^49 := by
    have hnat : (1964793517 : ℕ)^65*4000000000000^49 ≤ 461980078027^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964793517 10000000000 461980078027 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236439701/1250000000 : ℝ)^65 ≤ (1098163087851/10000000000000 : ℝ)^49 := by
    have hnat : (236439701 : ℕ)^65*10000000000000^49 ≤ 1098163087851^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236439701 1250000000 1098163087851 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1649867113/2000000000 : ℝ), (1964793517/10000000000 : ℝ), (236439701/1250000000 : ℝ)] ![(77468867160591/100000000000000 : ℝ), (461980078027/4000000000000 : ℝ), (1098163087851/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1649867113/2000000000 : ℝ)|^65 ≤ (77468867160591/100000000000000 : ℝ)^49
        have hw : |(1649867113/2000000000 : ℝ)|=(1649867113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1964793517/10000000000 : ℝ)|^65 ≤ (461980078027/4000000000000 : ℝ)^49
        have hw : |(1964793517/10000000000 : ℝ)|=(1964793517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(236439701/1250000000 : ℝ)|^65 ≤ (1098163087851/10000000000000 : ℝ)^49
        have hw : |(236439701/1250000000 : ℝ)|=(236439701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301061_s6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((17977/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17977/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74689/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74689/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35363/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35363/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11819/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11819/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16137/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16137/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29633/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29633/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (17977/25000 : ℝ) ^ (129/32 : ℝ) ≤ (13231318725011684673/50000000000000000000 : ℝ) := by
    have hpowers : (17977/25000 : ℝ)^129 ≤ (13231318725011684673/50000000000000000000 : ℝ)^32 := by
      have hnat : (17977 : ℕ)^129*50000000000000000000^32 ≤ 13231318725011684673^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17977 25000 13231318725011684673 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17977/25000 : ℝ)) (X := (13231318725011684673/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner0a : (63231318725011684673/50000000000000000000 : ℝ) ≤ (5299842480164513/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (63231318725011684673/50000000000000000000 : ℝ)^32 ≤ (5299842480164513/5000000000000000 : ℝ)^129 := by
      have hnat : (63231318725011684673 : ℕ)^32*5000000000000000^129 ≤ 5299842480164513^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63231318725011684673 50000000000000000000 5299842480164513 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5299842480164513/5000000000000000 : ℝ)) (X := (63231318725011684673/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner0b : (38231318725011684673/25000000000000000000 : ℝ) ≤ (11111234145058297/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (38231318725011684673/25000000000000000000 : ℝ)^32 ≤ (11111234145058297/10000000000000000 : ℝ)^129 := by
      have hnat : (38231318725011684673 : ℕ)^32*10000000000000000^129 ≤ 11111234145058297^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38231318725011684673 25000000000000000000 11111234145058297 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11111234145058297/10000000000000000 : ℝ)) (X := (38231318725011684673/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(299842480164513/3595400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(511549184729271/7190800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (17977/25000 : ℝ)) (alpha := (299842480164513/3595400000000000 : ℝ)) (beta := (511549184729271/7190800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17977/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(299842480164513/3595400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(511549184729271/7190800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (74689/100000 : ℝ) ^ (129/32 : ℝ) ≤ (1541827734689684429/5000000000000000000 : ℝ) := by
    have hpowers : (74689/100000 : ℝ)^129 ≤ (1541827734689684429/5000000000000000000 : ℝ)^32 := by
      have hnat : (74689 : ℕ)^129*5000000000000000000^32 ≤ 1541827734689684429^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74689 100000 1541827734689684429 5000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74689/100000 : ℝ)) (X := (1541827734689684429/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner1a : (6541827734689684429/5000000000000000000 : ℝ) ≤ (10689467117487741/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (6541827734689684429/5000000000000000000 : ℝ)^32 ≤ (10689467117487741/10000000000000000 : ℝ)^129 := by
      have hnat : (6541827734689684429 : ℕ)^32*10000000000000000^129 ≤ 10689467117487741^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6541827734689684429 5000000000000000000 10689467117487741 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10689467117487741/10000000000000000 : ℝ)) (X := (6541827734689684429/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner1b : (4041827734689684429/2500000000000000000 : ℝ) ≤ (1408202542022427/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (4041827734689684429/2500000000000000000 : ℝ)^32 ≤ (1408202542022427/1250000000000000 : ℝ)^129 := by
      have hnat : (4041827734689684429 : ℕ)^32*1250000000000000^129 ≤ 1408202542022427^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4041827734689684429 2500000000000000000 1408202542022427 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1408202542022427/1250000000000000 : ℝ)) (X := (4041827734689684429/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(689467117487741/7468900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(23046128747667/298756000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (74689/100000 : ℝ)) (alpha := (689467117487741/7468900000000000 : ℝ)) (beta := (23046128747667/298756000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (74689/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(689467117487741/7468900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(23046128747667/298756000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (35363/50000 : ℝ) ^ (129/32 : ℝ) ≤ (12376154943442006681/50000000000000000000 : ℝ) := by
    have hpowers : (35363/50000 : ℝ)^129 ≤ (12376154943442006681/50000000000000000000 : ℝ)^32 := by
      have hnat : (35363 : ℕ)^129*50000000000000000000^32 ≤ 12376154943442006681^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35363 50000 12376154943442006681 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35363/50000 : ℝ)) (X := (12376154943442006681/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner2a : (62376154943442006681/50000000000000000000 : ℝ) ≤ (2640985500771969/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (62376154943442006681/50000000000000000000 : ℝ)^32 ≤ (2640985500771969/2500000000000000 : ℝ)^129 := by
      have hnat : (62376154943442006681 : ℕ)^32*2500000000000000^129 ≤ 2640985500771969^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62376154943442006681 50000000000000000000 2640985500771969 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2640985500771969/2500000000000000 : ℝ)) (X := (62376154943442006681/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner2b : (37376154943442006681/25000000000000000000 : ℝ) ≤ (11049056014024893/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (37376154943442006681/25000000000000000000 : ℝ)^32 ≤ (11049056014024893/10000000000000000 : ℝ)^129 := by
      have hnat : (37376154943442006681 : ℕ)^32*10000000000000000^129 ≤ 11049056014024893^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37376154943442006681 25000000000000000000 11049056014024893 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11049056014024893/10000000000000000 : ℝ)) (X := (37376154943442006681/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(140985500771969/1768150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(485114010937017/7072600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (35363/50000 : ℝ)) (alpha := (140985500771969/1768150000000000 : ℝ)) (beta := (485114010937017/7072600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35363/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(140985500771969/1768150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(485114010937017/7072600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-29354539/156250000 : ℝ)*X 0 0+(2340034467/5000000000 : ℝ)*X 0 1+(308029481/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((600671983/1250000000 : ℝ)*X 1 0+(-1949637167/10000000000 : ℝ)*X 1 1+(5996386753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((4897980257/10000000000 : ℝ)*X 2 0+(1321269397/2000000000 : ℝ)*X 2 1+(-799399483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((6318896627/10000000000 : ℝ)*X 0 0+(2996344231/10000000000 : ℝ)*X 0 1+(444769667/1250000000 : ℝ)*X 0 2+(6318896627/10000000000 : ℝ)*X 1 0+(2996344231/10000000000 : ℝ)*X 1 1+(444769667/1250000000 : ℝ)*X 1 2+(6318896627/10000000000 : ℝ)*X 2 0+(2996344231/10000000000 : ℝ)*X 2 1+(444769667/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-1653324449/10000000000 : ℝ)*X 0 0+(3758047007/10000000000 : ℝ)*X 0 1+(7102151483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((821057389/2000000000 : ℝ)*X 1 0+(-1249282557/10000000000 : ℝ)*X 1 1+(3528126841/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((131295953/312500000 : ℝ)*X 2 0+(187642703/250000000 : ℝ)*X 2 1+(-2224039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((5523332683/10000000000 : ℝ)*X 0 0+(41429137/80000000 : ℝ)*X 0 1+(132112903/625000000 : ℝ)*X 0 2+(5523332683/10000000000 : ℝ)*X 1 0+(41429137/80000000 : ℝ)*X 1 1+(132112903/625000000 : ℝ)*X 1 2+(5523332683/10000000000 : ℝ)*X 2 0+(41429137/80000000 : ℝ)*X 2 1+(132112903/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-770901997/10000000000 : ℝ)*X 0 0+(3970708413/10000000000 : ℝ)*X 0 1+(7418457669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((710791527/2000000000 : ℝ)*X 1 0+(-11567939/78125000 : ℝ)*X 1 1+(921274333/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((6630423709/10000000000 : ℝ)*X 2 0+(5193078731/10000000000 : ℝ)*X 2 1+(-26003989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((158101669/200000000 : ℝ)*X 0 0+(2465198633/10000000000 : ℝ)*X 0 1+(958917577/5000000000 : ℝ)*X 0 2+(158101669/200000000 : ℝ)*X 1 0+(2465198633/10000000000 : ℝ)*X 1 1+(958917577/5000000000 : ℝ)*X 1 2+(158101669/200000000 : ℝ)*X 2 0+(2465198633/10000000000 : ℝ)*X 2 1+(958917577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-490922671/10000000000 : ℝ)*X 0 0+(762105641/1250000000 : ℝ)*X 0 1+(1398908747/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((6536060587/10000000000 : ℝ)*X 1 0+(-552903459/10000000000 : ℝ)*X 1 1+(5102922487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((3804491939/10000000000 : ℝ)*X 2 0+(7725562507/10000000000 : ℝ)*X 2 1+(-4561889/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((1649867113/2000000000 : ℝ)*X 0 0+(1964793517/10000000000 : ℝ)*X 0 1+(236439701/1250000000 : ℝ)*X 0 2+(1649867113/2000000000 : ℝ)*X 1 0+(1964793517/10000000000 : ℝ)*X 1 1+(236439701/1250000000 : ℝ)*X 1 2+(1649867113/2000000000 : ℝ)*X 2 0+(1964793517/10000000000 : ℝ)*X 2 1+(236439701/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((11819/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11819/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1247829661775528531899859271/63572065100000000000000000000000 : ℝ) := by norm_num
    linear_combination (25610003183/250000000000 : ℝ)*(base7) + (58094855711/200000000000 : ℝ)*(base59) + (1908989452713/500000000000 : ℝ)*(major_s6_0) + (1908989452713/500000000000 : ℝ)*(major_s6_1) + (1908989452713/500000000000 : ℝ)*(major_s6_2) + (45477717/1000000000000 : ℝ)*(sp_s6_0) + (20667/800000000 : ℝ)*(sp_s6_1) + (21147899/1000000000000 : ℝ)*(sp_s6_6) + (4991682386151/1000000000000 : ℝ)*(sp_s6_7) + (311984423383/62500000000 : ℝ)*(sp_s6_8) + (4991813490537/1000000000000 : ℝ)*(sp_s6_9) + (2683459740841/1000000000000 : ℝ)*(sp_s6_13) + (85626669/1000000000000 : ℝ)*(sp_s6_14) + (1844133/50000000000 : ℝ)*(sp_s6_15) + (322630109501/125000000000 : ℝ)*(f.failure) + (4991813490537/1000000000000 : ℝ)*(f.sum) + (139923601882473799/1056490842800000000000000000000 : ℝ)*base62 + (289355114785501/3536300000000000000000000000 : ℝ)*base64 + (289805052065181/746890000000000000000000000 : ℝ)*base67 + (120712311929023/884075000000000000000000000 : ℝ)*base68 + (480031675639665967/1271441302000000000000000000000 : ℝ)*base70 + (1262609815823497/3595400000000000000000000000 : ℝ)*base72 + (932652983001873/3734450000000000000000000000 : ℝ)*base75 + (786211473947589/1797700000000000000000000000 : ℝ)*base77 + (18878610033866379993/268536830600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (231/3125000000000000 : ℝ)*base87 + (231/3125000000000000 : ℝ)*base89 + (231/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16137/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16137/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (128186113619681304585063819332379/9496267940507800000000000000000000000 : ℝ) := by norm_num
    linear_combination (353715247147/1000000000000 : ℝ)*(base7) + (639693/500000000000 : ℝ)*(base40) + (12843573/1000000000000 : ℝ)*(base53) + (5138117/1000000000000 : ℝ)*(base59) + (540621184319/200000000000 : ℝ)*(major_s6_0) + (540621184319/200000000000 : ℝ)*(major_s6_1) + (1351546539011/500000000000 : ℝ)*(major_s6_2) + (32243021/1000000000000 : ℝ)*(sp_s6_7) + (74946579/1000000000000 : ℝ)*(sp_s6_8) + (3360933593019/1000000000000 : ℝ)*(sp_s6_14) + (168044544473/50000000000 : ℝ)*(sp_s6_15) + (840244669903/250000000000 : ℝ)*(sp_s6_16) + (272620626693/125000000000 : ℝ)*(sp_s6_20) + (55764159/500000000000 : ℝ)*(sp_s6_27) + (365472258943/200000000000 : ℝ)*(f.failure) + (840244669903/250000000000 : ℝ)*(f.sum) + (85371345608733125229/264122710700000000000000000000000 : ℝ)*base63 + (175743598320053/3536300000000000000000000000 : ℝ)*base65 + (53049622992153/1493780000000000000000000000 : ℝ)*base67 + (1308339252964443/1768150000000000000000000000 : ℝ)*base69 + (61347822616414812793/127144130200000000000000000000000 : ℝ)*base70 + (1570546617806041/1438160000000000000000000000 : ℝ)*base73 + (260526123920499/298756000000000000000000000 : ℝ)*base75 + (235881282667607/719080000000000000000000000 : ℝ)*base77 + (9296565386838037529/21482946448000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (3917/5000000000000000 : ℝ)*base86 + (3917/5000000000000000 : ℝ)*base88 + (3917/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29633/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29633/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (170505026249455418065760223/12714413020000000000000000000000 : ℝ) := by norm_num
    linear_combination (143316237933/1000000000000 : ℝ)*(base7) + (4056003/500000000000 : ℝ)*(base11) + (39435978611/250000000000 : ℝ)*(base40) + (412197397/200000000000 : ℝ)*(base59) + (273661930339/100000000000 : ℝ)*(major_s6_0) + (273661930339/100000000000 : ℝ)*(major_s6_1) + (273661930339/100000000000 : ℝ)*(major_s6_2) + (4512019/1000000000000 : ℝ)*(sp_s6_1) + (1394907/1000000000000 : ℝ)*(sp_s6_2) + (47314769/250000000000 : ℝ)*(sp_s6_9) + (3534934715381/1000000000000 : ℝ)*(sp_s6_21) + (3534938315369/1000000000000 : ℝ)*(sp_s6_22) + (883688043351/250000000000 : ℝ)*(sp_s6_23) + (996666671801/500000000000 : ℝ)*(sp_s6_27) + (1850017105669/1000000000000 : ℝ)*(f.failure) + (883735706847/250000000000 : ℝ)*(f.sum) + (4054659610503164209/13206135535000000000000000000000 : ℝ)*base62 + (28259132381557/141452000000000000000000000 : ℝ)*base65 + (190145101699909/746890000000000000000000000 : ℝ)*base67 + (17555370724421/70726000000000000000000000 : ℝ)*base68 + (198392803365950159/1271441302000000000000000000000 : ℝ)*base70 + (299990481164739/719080000000000000000000000 : ℝ)*base72 + (13415935613459/74689000000000000000000000 : ℝ)*base75 + (345627721038449/359540000000000000000000000 : ℝ)*base77 + (22181601347057143651/53707366120000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (4711/25000000000000000 : ℝ)*base86 + (4711/25000000000000000 : ℝ)*base88 + (4711/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((17977/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17977/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74689/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74689/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35363/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35363/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11819/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11819/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16137/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16137/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29633/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29633/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301061_s6 p hpa hpb X hX hprev5

#print axioms solution
