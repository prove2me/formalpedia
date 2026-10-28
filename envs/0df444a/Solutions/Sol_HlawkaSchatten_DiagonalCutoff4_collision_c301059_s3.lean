-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301059_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:35:39.44998+00:00
-- url     : https://prove2.me/submissions/0f827c65-003a-43da-9d92-c7012edd98a7

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
theorem collision_support_c301059_s3_s3_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3127223949/10000000000 : ℝ)*x 0 + (1564296369/5000000000 : ℝ)*x 1 + (3281479523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3127223949/10000000000 : ℝ)^65 ≤ (21395031838999/100000000000000 : ℝ)^49 := by
    have hnat : (3127223949 : ℕ)^65*100000000000000^49 ≤ 21395031838999^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3127223949 10000000000 21395031838999 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1564296369/5000000000 : ℝ)^65 ≤ (21407455190351/100000000000000 : ℝ)^49 := by
    have hnat : (1564296369 : ℕ)^65*100000000000000^49 ≤ 21407455190351^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564296369 5000000000 21407455190351 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3281479523/5000000000 : ℝ)^65 ≤ (11439502591413/20000000000000 : ℝ)^49 := by
    have hnat : (3281479523 : ℕ)^65*20000000000000^49 ≤ 11439502591413^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3281479523 5000000000 11439502591413 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3127223949/10000000000 : ℝ), (1564296369/5000000000 : ℝ), (3281479523/5000000000 : ℝ)] ![(21395031838999/100000000000000 : ℝ), (21407455190351/100000000000000 : ℝ), (11439502591413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3127223949/10000000000 : ℝ)|^65 ≤ (21395031838999/100000000000000 : ℝ)^49
        have hw : |(-3127223949/10000000000 : ℝ)|=(3127223949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1564296369/5000000000 : ℝ)|^65 ≤ (21407455190351/100000000000000 : ℝ)^49
        have hw : |(1564296369/5000000000 : ℝ)|=(1564296369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3281479523/5000000000 : ℝ)|^65 ≤ (11439502591413/20000000000000 : ℝ)^49
        have hw : |(3281479523/5000000000 : ℝ)|=(3281479523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3127897841/10000000000 : ℝ)*x 0 + (-1565019869/5000000000 : ℝ)*x 1 + (820161723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3127897841/10000000000 : ℝ)^65 ≤ (167196468519/781250000000 : ℝ)^49 := by
    have hnat : (3127897841 : ℕ)^65*781250000000^49 ≤ 167196468519^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3127897841 10000000000 167196468519 781250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1565019869/5000000000 : ℝ)^65 ≤ (5355147581847/25000000000000 : ℝ)^49 := by
    have hnat : (1565019869 : ℕ)^65*25000000000000^49 ≤ 5355147581847^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565019869 5000000000 5355147581847 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820161723/1250000000 : ℝ)^65 ≤ (14294565422631/25000000000000 : ℝ)^49 := by
    have hnat : (820161723 : ℕ)^65*25000000000000^49 ≤ 14294565422631^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820161723 1250000000 14294565422631 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3127897841/10000000000 : ℝ), (-1565019869/5000000000 : ℝ), (820161723/1250000000 : ℝ)] ![(167196468519/781250000000 : ℝ), (5355147581847/25000000000000 : ℝ), (14294565422631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3127897841/10000000000 : ℝ)|^65 ≤ (167196468519/781250000000 : ℝ)^49
        have hw : |(3127897841/10000000000 : ℝ)|=(3127897841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1565019869/5000000000 : ℝ)|^65 ≤ (5355147581847/25000000000000 : ℝ)^49
        have hw : |(-1565019869/5000000000 : ℝ)|=(1565019869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(820161723/1250000000 : ℝ)|^65 ≤ (14294565422631/25000000000000 : ℝ)^49
        have hw : |(820161723/1250000000 : ℝ)|=(820161723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1839421023/10000000000 : ℝ)*x 0 + (313505979/2500000000 : ℝ)*x 1 + (4346813487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1839421023/10000000000 : ℝ)^65 ≤ (10582225946283/100000000000000 : ℝ)^49 := by
    have hnat : (1839421023 : ℕ)^65*100000000000000^49 ≤ 10582225946283^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839421023 10000000000 10582225946283 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313505979/2500000000 : ℝ)^65 ≤ (6366123599249/100000000000000 : ℝ)^49 := by
    have hnat : (313505979 : ℕ)^65*100000000000000^49 ≤ 6366123599249^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313505979 2500000000 6366123599249 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4346813487/5000000000 : ℝ)^65 ≤ (83051650439649/100000000000000 : ℝ)^49 := by
    have hnat : (4346813487 : ℕ)^65*100000000000000^49 ≤ 83051650439649^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346813487 5000000000 83051650439649 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1839421023/10000000000 : ℝ), (313505979/2500000000 : ℝ), (4346813487/5000000000 : ℝ)] ![(10582225946283/100000000000000 : ℝ), (6366123599249/100000000000000 : ℝ), (83051650439649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1839421023/10000000000 : ℝ)|^65 ≤ (10582225946283/100000000000000 : ℝ)^49
        have hw : |(-1839421023/10000000000 : ℝ)|=(1839421023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(313505979/2500000000 : ℝ)|^65 ≤ (6366123599249/100000000000000 : ℝ)^49
        have hw : |(313505979/2500000000 : ℝ)|=(313505979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4346813487/5000000000 : ℝ)|^65 ≤ (83051650439649/100000000000000 : ℝ)^49
        have hw : |(4346813487/5000000000 : ℝ)|=(4346813487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (337560903/2000000000 : ℝ)*x 0 + (-355998557/2500000000 : ℝ)*x 1 + (8691416263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337560903/2000000000 : ℝ)^65 ≤ (9441025508309/100000000000000 : ℝ)^49 := by
    have hnat : (337560903 : ℕ)^65*100000000000000^49 ≤ 9441025508309^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337560903 2000000000 9441025508309 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355998557/2500000000 : ℝ)^65 ≤ (301413530529/4000000000000 : ℝ)^49 := by
    have hnat : (355998557 : ℕ)^65*4000000000000^49 ≤ 301413530529^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355998557 2500000000 301413530529 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8691416263/10000000000 : ℝ)^65 ≤ (83023636223019/100000000000000 : ℝ)^49 := by
    have hnat : (8691416263 : ℕ)^65*100000000000000^49 ≤ 83023636223019^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8691416263 10000000000 83023636223019 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337560903/2000000000 : ℝ), (-355998557/2500000000 : ℝ), (8691416263/10000000000 : ℝ)] ![(9441025508309/100000000000000 : ℝ), (301413530529/4000000000000 : ℝ), (83023636223019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337560903/2000000000 : ℝ)|^65 ≤ (9441025508309/100000000000000 : ℝ)^49
        have hw : |(337560903/2000000000 : ℝ)|=(337560903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-355998557/2500000000 : ℝ)|^65 ≤ (301413530529/4000000000000 : ℝ)^49
        have hw : |(-355998557/2500000000 : ℝ)|=(355998557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8691416263/10000000000 : ℝ)|^65 ≤ (83023636223019/100000000000000 : ℝ)^49
        have hw : |(8691416263/10000000000 : ℝ)|=(8691416263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (131339571/312500000 : ℝ)*x 0 + (187607259/250000000 : ℝ)*x 1 + (-1075193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131339571/312500000 : ℝ)^65 ≤ (31668075871757/100000000000000 : ℝ)^49 := by
    have hnat : (131339571 : ℕ)^65*100000000000000^49 ≤ 31668075871757^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131339571 312500000 31668075871757 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187607259/250000000 : ℝ)^65 ≤ (68327323136831/100000000000000 : ℝ)^49 := by
    have hnat : (187607259 : ℕ)^65*100000000000000^49 ≤ 68327323136831^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187607259 250000000 68327323136831 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075193/2000000000 : ℝ)^65 ≤ (2300490129/50000000000000 : ℝ)^49 := by
    have hnat : (1075193 : ℕ)^65*50000000000000^49 ≤ 2300490129^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075193 2000000000 2300490129 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131339571/312500000 : ℝ), (187607259/250000000 : ℝ), (-1075193/2000000000 : ℝ)] ![(31668075871757/100000000000000 : ℝ), (68327323136831/100000000000000 : ℝ), (2300490129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131339571/312500000 : ℝ)|^65 ≤ (31668075871757/100000000000000 : ℝ)^49
        have hw : |(131339571/312500000 : ℝ)|=(131339571/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(187607259/250000000 : ℝ)|^65 ≤ (68327323136831/100000000000000 : ℝ)^49
        have hw : |(187607259/250000000 : ℝ)|=(187607259/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075193/2000000000 : ℝ)|^65 ≤ (2300490129/50000000000000 : ℝ)^49
        have hw : |(-1075193/2000000000 : ℝ)|=(1075193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (39921433/200000000 : ℝ)*x 0 + (411490811/500000000 : ℝ)*x 1 + (945663867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39921433/200000000 : ℝ)^65 ≤ (11794029468183/100000000000000 : ℝ)^49 := by
    have hnat : (39921433 : ℕ)^65*100000000000000^49 ≤ 11794029468183^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39921433 200000000 11794029468183 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411490811/500000000 : ℝ)^65 ≤ (77225801920497/100000000000000 : ℝ)^49 := by
    have hnat : (411490811 : ℕ)^65*100000000000000^49 ≤ 77225801920497^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411490811 500000000 77225801920497 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945663867/5000000000 : ℝ)^65 ≤ (5490084296609/50000000000000 : ℝ)^49 := by
    have hnat : (945663867 : ℕ)^65*50000000000000^49 ≤ 5490084296609^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945663867 5000000000 5490084296609 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(39921433/200000000 : ℝ), (411490811/500000000 : ℝ), (945663867/5000000000 : ℝ)] ![(11794029468183/100000000000000 : ℝ), (77225801920497/100000000000000 : ℝ), (5490084296609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(39921433/200000000 : ℝ)|^65 ≤ (11794029468183/100000000000000 : ℝ)^49
        have hw : |(39921433/200000000 : ℝ)|=(39921433/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(411490811/500000000 : ℝ)|^65 ≤ (77225801920497/100000000000000 : ℝ)^49
        have hw : |(411490811/500000000 : ℝ)|=(411490811/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(945663867/5000000000 : ℝ)|^65 ≤ (5490084296609/50000000000000 : ℝ)^49
        have hw : |(945663867/5000000000 : ℝ)|=(945663867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-202268757/1250000000 : ℝ)*x 0 + (1918579197/10000000000 : ℝ)*x 1 + (4221148133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202268757/1250000000 : ℝ)^65 ≤ (89276923231/1000000000000 : ℝ)^49 := by
    have hnat : (202268757 : ℕ)^65*1000000000000^49 ≤ 89276923231^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202268757 1250000000 89276923231 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1918579197/10000000000 : ℝ)^65 ≤ (11190530203917/100000000000000 : ℝ)^49 := by
    have hnat : (1918579197 : ℕ)^65*100000000000000^49 ≤ 11190530203917^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918579197 10000000000 11190530203917 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221148133/5000000000 : ℝ)^65 ≤ (19970444364849/25000000000000 : ℝ)^49 := by
    have hnat : (4221148133 : ℕ)^65*25000000000000^49 ≤ 19970444364849^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221148133 5000000000 19970444364849 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202268757/1250000000 : ℝ), (1918579197/10000000000 : ℝ), (4221148133/5000000000 : ℝ)] ![(89276923231/1000000000000 : ℝ), (11190530203917/100000000000000 : ℝ), (19970444364849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202268757/1250000000 : ℝ)|^65 ≤ (89276923231/1000000000000 : ℝ)^49
        have hw : |(-202268757/1250000000 : ℝ)|=(202268757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1918579197/10000000000 : ℝ)|^65 ≤ (11190530203917/100000000000000 : ℝ)^49
        have hw : |(1918579197/10000000000 : ℝ)|=(1918579197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221148133/5000000000 : ℝ)|^65 ≤ (19970444364849/25000000000000 : ℝ)^49
        have hw : |(4221148133/5000000000 : ℝ)|=(4221148133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (768381787/5000000000 : ℝ)*x 0 + (-1997871849/10000000000 : ℝ)*x 1 + (4220076107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (768381787/5000000000 : ℝ)^65 ≤ (8336991572289/100000000000000 : ℝ)^49 := by
    have hnat : (768381787 : ℕ)^65*100000000000000^49 ≤ 8336991572289^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768381787 5000000000 8336991572289 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997871849/10000000000 : ℝ)^65 ≤ (5904070721691/50000000000000 : ℝ)^49 := by
    have hnat : (1997871849 : ℕ)^65*50000000000000^49 ≤ 5904070721691^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997871849 10000000000 5904070721691 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4220076107/5000000000 : ℝ)^65 ≤ (1247732296293/1562500000000 : ℝ)^49 := by
    have hnat : (4220076107 : ℕ)^65*1562500000000^49 ≤ 1247732296293^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220076107 5000000000 1247732296293 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(768381787/5000000000 : ℝ), (-1997871849/10000000000 : ℝ), (4220076107/5000000000 : ℝ)] ![(8336991572289/100000000000000 : ℝ), (5904070721691/50000000000000 : ℝ), (1247732296293/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(768381787/5000000000 : ℝ)|^65 ≤ (8336991572289/100000000000000 : ℝ)^49
        have hw : |(768381787/5000000000 : ℝ)|=(768381787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997871849/10000000000 : ℝ)|^65 ≤ (5904070721691/50000000000000 : ℝ)^49
        have hw : |(-1997871849/10000000000 : ℝ)|=(1997871849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4220076107/5000000000 : ℝ)|^65 ≤ (1247732296293/1562500000000 : ℝ)^49
        have hw : |(4220076107/5000000000 : ℝ)|=(4220076107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4293199529/5000000000 : ℝ)*x 0 + (139011663/500000000 : ℝ)*x 1 + (1799/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4293199529/5000000000 : ℝ)^65 ≤ (10211942704151/12500000000000 : ℝ)^49 := by
    have hnat : (4293199529 : ℕ)^65*12500000000000^49 ≤ 10211942704151^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293199529 5000000000 10211942704151 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139011663/500000000 : ℝ)^65 ≤ (915222617241/5000000000000 : ℝ)^49 := by
    have hnat : (139011663 : ℕ)^65*5000000000000^49 ≤ 915222617241^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139011663 500000000 915222617241 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1799/500000000 : ℝ)^65 ≤ (1501027/25000000000000 : ℝ)^49 := by
    have hnat : (1799 : ℕ)^65*25000000000000^49 ≤ 1501027^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799 500000000 1501027 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4293199529/5000000000 : ℝ), (139011663/500000000 : ℝ), (1799/500000000 : ℝ)] ![(10211942704151/12500000000000 : ℝ), (915222617241/5000000000000 : ℝ), (1501027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4293199529/5000000000 : ℝ)|^65 ≤ (10211942704151/12500000000000 : ℝ)^49
        have hw : |(4293199529/5000000000 : ℝ)|=(4293199529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(139011663/500000000 : ℝ)|^65 ≤ (915222617241/5000000000000 : ℝ)^49
        have hw : |(139011663/500000000 : ℝ)|=(139011663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1799/500000000 : ℝ)|^65 ≤ (1501027/25000000000000 : ℝ)^49
        have hw : |(1799/500000000 : ℝ)|=(1799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (133444517/200000000 : ℝ)*x 0 + (3872291397/10000000000 : ℝ)*x 1 + (2164091243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133444517/200000000 : ℝ)^65 ≤ (58464165498607/100000000000000 : ℝ)^49 := by
    have hnat : (133444517 : ℕ)^65*100000000000000^49 ≤ 58464165498607^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133444517 200000000 58464165498607 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3872291397/10000000000 : ℝ)^65 ≤ (1775444077961/6250000000000 : ℝ)^49 := by
    have hnat : (3872291397 : ℕ)^65*6250000000000^49 ≤ 1775444077961^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3872291397 10000000000 1775444077961 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2164091243/10000000000 : ℝ)^65 ≤ (6564364620571/50000000000000 : ℝ)^49 := by
    have hnat : (2164091243 : ℕ)^65*50000000000000^49 ≤ 6564364620571^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164091243 10000000000 6564364620571 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133444517/200000000 : ℝ), (3872291397/10000000000 : ℝ), (2164091243/10000000000 : ℝ)] ![(58464165498607/100000000000000 : ℝ), (1775444077961/6250000000000 : ℝ), (6564364620571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133444517/200000000 : ℝ)|^65 ≤ (58464165498607/100000000000000 : ℝ)^49
        have hw : |(133444517/200000000 : ℝ)|=(133444517/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3872291397/10000000000 : ℝ)|^65 ≤ (1775444077961/6250000000000 : ℝ)^49
        have hw : |(3872291397/10000000000 : ℝ)|=(3872291397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2164091243/10000000000 : ℝ)|^65 ≤ (6564364620571/50000000000000 : ℝ)^49
        have hw : |(2164091243/10000000000 : ℝ)|=(2164091243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-6052725679/10000000000 : ℝ)*x 0 + (2573520619/10000000000 : ℝ)*x 1 + (849274411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6052725679/10000000000 : ℝ)^65 ≤ (12843734625117/25000000000000 : ℝ)^49 := by
    have hnat : (6052725679 : ℕ)^65*25000000000000^49 ≤ 12843734625117^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6052725679 10000000000 12843734625117 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2573520619/10000000000 : ℝ)^65 ≤ (16521401501733/100000000000000 : ℝ)^49 := by
    have hnat : (2573520619 : ℕ)^65*100000000000000^49 ≤ 16521401501733^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573520619 10000000000 16521401501733 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849274411/2000000000 : ℝ)^65 ≤ (6420731996331/20000000000000 : ℝ)^49 := by
    have hnat : (849274411 : ℕ)^65*20000000000000^49 ≤ 6420731996331^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849274411 2000000000 6420731996331 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6052725679/10000000000 : ℝ), (2573520619/10000000000 : ℝ), (849274411/2000000000 : ℝ)] ![(12843734625117/25000000000000 : ℝ), (16521401501733/100000000000000 : ℝ), (6420731996331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6052725679/10000000000 : ℝ)|^65 ≤ (12843734625117/25000000000000 : ℝ)^49
        have hw : |(-6052725679/10000000000 : ℝ)|=(6052725679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2573520619/10000000000 : ℝ)|^65 ≤ (16521401501733/100000000000000 : ℝ)^49
        have hw : |(2573520619/10000000000 : ℝ)|=(2573520619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849274411/2000000000 : ℝ)|^65 ≤ (6420731996331/20000000000000 : ℝ)^49
        have hw : |(849274411/2000000000 : ℝ)|=(849274411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (744692887/5000000000 : ℝ)*x 0 + (-596340533/2500000000 : ℝ)*x 1 + (8216793557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (744692887/5000000000 : ℝ)^65 ≤ (999720849283/12500000000000 : ℝ)^49 := by
    have hnat : (744692887 : ℕ)^65*12500000000000^49 ≤ 999720849283^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744692887 5000000000 999720849283 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596340533/2500000000 : ℝ)^65 ≤ (3734622938143/25000000000000 : ℝ)^49 := by
    have hnat : (596340533 : ℕ)^65*25000000000000^49 ≤ 3734622938143^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596340533 2500000000 3734622938143 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8216793557/10000000000 : ℝ)^65 ≤ (77063741442613/100000000000000 : ℝ)^49 := by
    have hnat : (8216793557 : ℕ)^65*100000000000000^49 ≤ 77063741442613^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8216793557 10000000000 77063741442613 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(744692887/5000000000 : ℝ), (-596340533/2500000000 : ℝ), (8216793557/10000000000 : ℝ)] ![(999720849283/12500000000000 : ℝ), (3734622938143/25000000000000 : ℝ), (77063741442613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(744692887/5000000000 : ℝ)|^65 ≤ (999720849283/12500000000000 : ℝ)^49
        have hw : |(744692887/5000000000 : ℝ)|=(744692887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-596340533/2500000000 : ℝ)|^65 ≤ (3734622938143/25000000000000 : ℝ)^49
        have hw : |(-596340533/2500000000 : ℝ)|=(596340533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8216793557/10000000000 : ℝ)|^65 ≤ (77063741442613/100000000000000 : ℝ)^49
        have hw : |(8216793557/10000000000 : ℝ)|=(8216793557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4155588211/5000000000 : ℝ)*x 0 + (1580446891/5000000000 : ℝ)*x 1 + (18319267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155588211/5000000000 : ℝ)^65 ≤ (39120090686733/50000000000000 : ℝ)^49 := by
    have hnat : (4155588211 : ℕ)^65*50000000000000^49 ≤ 39120090686733^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155588211 5000000000 39120090686733 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1580446891/5000000000 : ℝ)^65 ≤ (1356321170471/6250000000000 : ℝ)^49 := by
    have hnat : (1580446891 : ℕ)^65*6250000000000^49 ≤ 1356321170471^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580446891 5000000000 1356321170471 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18319267/5000000000 : ℝ)^65 ≤ (58679891287/100000000000000 : ℝ)^49 := by
    have hnat : (18319267 : ℕ)^65*100000000000000^49 ≤ 58679891287^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18319267 5000000000 58679891287 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155588211/5000000000 : ℝ), (1580446891/5000000000 : ℝ), (18319267/5000000000 : ℝ)] ![(39120090686733/50000000000000 : ℝ), (1356321170471/6250000000000 : ℝ), (58679891287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155588211/5000000000 : ℝ)|^65 ≤ (39120090686733/50000000000000 : ℝ)^49
        have hw : |(4155588211/5000000000 : ℝ)|=(4155588211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1580446891/5000000000 : ℝ)|^65 ≤ (1356321170471/6250000000000 : ℝ)^49
        have hw : |(1580446891/5000000000 : ℝ)|=(1580446891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18319267/5000000000 : ℝ)|^65 ≤ (58679891287/100000000000000 : ℝ)^49
        have hw : |(18319267/5000000000 : ℝ)|=(18319267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s3_s3_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (84377673/400000000 : ℝ)*x 0 + (1894592717/2500000000 : ℝ)*x 1 + (2755151387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84377673/400000000 : ℝ)^65 ≤ (6345379107169/50000000000000 : ℝ)^49 := by
    have hnat : (84377673 : ℕ)^65*50000000000000^49 ≤ 6345379107169^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84377673 400000000 6345379107169 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894592717/2500000000 : ℝ)^65 ≤ (69223520906093/100000000000000 : ℝ)^49 := by
    have hnat : (1894592717 : ℕ)^65*100000000000000^49 ≤ 69223520906093^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894592717 2500000000 69223520906093 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755151387/10000000000 : ℝ)^65 ≤ (18085720860061/100000000000000 : ℝ)^49 := by
    have hnat : (2755151387 : ℕ)^65*100000000000000^49 ≤ 18085720860061^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755151387 10000000000 18085720860061 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84377673/400000000 : ℝ), (1894592717/2500000000 : ℝ), (2755151387/10000000000 : ℝ)] ![(6345379107169/50000000000000 : ℝ), (69223520906093/100000000000000 : ℝ), (18085720860061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84377673/400000000 : ℝ)|^65 ≤ (6345379107169/50000000000000 : ℝ)^49
        have hw : |(84377673/400000000 : ℝ)|=(84377673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1894592717/2500000000 : ℝ)|^65 ≤ (69223520906093/100000000000000 : ℝ)^49
        have hw : |(1894592717/2500000000 : ℝ)|=(1894592717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755151387/10000000000 : ℝ)|^65 ≤ (18085720860061/100000000000000 : ℝ)^49
        have hw : |(2755151387/10000000000 : ℝ)|=(2755151387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301059_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((45327/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45327/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11347/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11347/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7893/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7893/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((84819/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84819/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16909/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16909/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13693/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13693/20000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (45327/50000 : ℝ) ^ (129/32 : ℝ) ≤ (16832795136008828457/25000000000000000000 : ℝ) := by
    have hpowers : (45327/50000 : ℝ)^129 ≤ (16832795136008828457/25000000000000000000 : ℝ)^32 := by
      have hnat : (45327 : ℕ)^129*25000000000000000000^32 ≤ 16832795136008828457^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45327 50000 16832795136008828457 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45327/50000 : ℝ)) (X := (16832795136008828457/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (41832795136008828457/25000000000000000000 : ℝ) ≤ (5681080387270277/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (41832795136008828457/25000000000000000000 : ℝ)^32 ≤ (5681080387270277/5000000000000000 : ℝ)^129 := by
      have hnat : (41832795136008828457 : ℕ)^32*5000000000000000^129 ≤ 5681080387270277^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41832795136008828457 25000000000000000000 5681080387270277 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5681080387270277/5000000000000000 : ℝ)) (X := (41832795136008828457/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (29332795136008828457/12500000000000000000 : ℝ) ≤ (6178214035119341/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (29332795136008828457/12500000000000000000 : ℝ)^32 ≤ (6178214035119341/5000000000000000 : ℝ)^129 := by
      have hnat : (29332795136008828457 : ℕ)^32*5000000000000000^129 ≤ 6178214035119341^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29332795136008828457 12500000000000000000 6178214035119341 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6178214035119341/5000000000000000 : ℝ)) (X := (29332795136008828457/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(227026795756759/1510900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(20713901993711/188862500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (45327/50000 : ℝ)) (alpha := (227026795756759/1510900000000000 : ℝ)) (beta := (20713901993711/188862500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (45327/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(227026795756759/1510900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(20713901993711/188862500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (11347/12500 : ℝ) ^ (129/32 : ℝ) ≤ (6769720874806510381/10000000000000000000 : ℝ) := by
    have hpowers : (11347/12500 : ℝ)^129 ≤ (6769720874806510381/10000000000000000000 : ℝ)^32 := by
      have hnat : (11347 : ℕ)^129*10000000000000000000^32 ≤ 6769720874806510381^32*12500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11347 12500 6769720874806510381 10000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11347/12500 : ℝ)) (X := (6769720874806510381/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (16769720874806510381/10000000000000000000 : ℝ) ≤ (1136832107669021/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (16769720874806510381/10000000000000000000 : ℝ)^32 ≤ (1136832107669021/1000000000000000 : ℝ)^129 := by
      have hnat : (16769720874806510381 : ℕ)^32*1000000000000000^129 ≤ 1136832107669021^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16769720874806510381 10000000000000000000 1136832107669021 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1136832107669021/1000000000000000 : ℝ)) (X := (16769720874806510381/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (11769720874806510381/5000000000000000000 : ℝ) ≤ (12365978998373071/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (11769720874806510381/5000000000000000000 : ℝ)^32 ≤ (12365978998373071/10000000000000000 : ℝ)^129 := by
      have hnat : (11769720874806510381 : ℕ)^32*10000000000000000^129 ≤ 12365978998373071^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11769720874806510381 5000000000000000000 12365978998373071 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12365978998373071/10000000000000000 : ℝ)) (X := (11769720874806510381/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(136832107669021/907760000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(997657921682861/9077600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (11347/12500 : ℝ)) (alpha := (136832107669021/907760000000000 : ℝ)) (beta := (997657921682861/9077600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (11347/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(136832107669021/907760000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(997657921682861/9077600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (7893/10000 : ℝ) ^ (129/32 : ℝ) ≤ (38526293330611862267/100000000000000000000 : ℝ) := by
    have hpowers : (7893/10000 : ℝ)^129 ≤ (38526293330611862267/100000000000000000000 : ℝ)^32 := by
      have hnat : (7893 : ℕ)^129*100000000000000000000^32 ≤ 38526293330611862267^32*10000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7893 10000 38526293330611862267 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7893/10000 : ℝ)) (X := (38526293330611862267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (138526293330611862267/100000000000000000000 : ℝ) ≤ (10841984102895273/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (138526293330611862267/100000000000000000000 : ℝ)^32 ≤ (10841984102895273/10000000000000000 : ℝ)^129 := by
      have hnat : (138526293330611862267 : ℕ)^32*10000000000000000^129 ≤ 10841984102895273^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        138526293330611862267 100000000000000000000 10841984102895273 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10841984102895273/10000000000000000 : ℝ)) (X := (138526293330611862267/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (88526293330611862267/50000000000000000000 : ℝ) ≤ (5761223917403643/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (88526293330611862267/50000000000000000000 : ℝ)^32 ≤ (5761223917403643/5000000000000000 : ℝ)^129 := by
      have hnat : (88526293330611862267 : ℕ)^32*5000000000000000^129 ≤ 5761223917403643^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88526293330611862267 50000000000000000000 5761223917403643 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5761223917403643/5000000000000000 : ℝ)) (X := (88526293330611862267/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(841984102895273/7893000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(75607081323557/877000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (7893/10000 : ℝ)) (alpha := (841984102895273/7893000000000000 : ℝ)) (beta := (75607081323557/877000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (7893/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(841984102895273/7893000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(75607081323557/877000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-3127223949/10000000000 : ℝ)*X 0 0+(1564296369/5000000000 : ℝ)*X 0 1+(3281479523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((3127897841/10000000000 : ℝ)*X 1 0+(-1565019869/5000000000 : ℝ)*X 1 1+(820161723/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1839421023/10000000000 : ℝ)*X 0 0+(313505979/2500000000 : ℝ)*X 0 1+(4346813487/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((337560903/2000000000 : ℝ)*X 1 0+(-355998557/2500000000 : ℝ)*X 1 1+(8691416263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((131339571/312500000 : ℝ)*X 2 0+(187607259/250000000 : ℝ)*X 2 1+(-1075193/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((39921433/200000000 : ℝ)*X 0 0+(411490811/500000000 : ℝ)*X 0 1+(945663867/5000000000 : ℝ)*X 0 2+(39921433/200000000 : ℝ)*X 1 0+(411490811/500000000 : ℝ)*X 1 1+(945663867/5000000000 : ℝ)*X 1 2+(39921433/200000000 : ℝ)*X 2 0+(411490811/500000000 : ℝ)*X 2 1+(945663867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-202268757/1250000000 : ℝ)*X 0 0+(1918579197/10000000000 : ℝ)*X 0 1+(4221148133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((768381787/5000000000 : ℝ)*X 1 0+(-1997871849/10000000000 : ℝ)*X 1 1+(4220076107/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((4293199529/5000000000 : ℝ)*X 2 0+(139011663/500000000 : ℝ)*X 2 1+(1799/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((133444517/200000000 : ℝ)*X 0 0+(3872291397/10000000000 : ℝ)*X 0 1+(2164091243/10000000000 : ℝ)*X 0 2+(133444517/200000000 : ℝ)*X 1 0+(3872291397/10000000000 : ℝ)*X 1 1+(2164091243/10000000000 : ℝ)*X 1 2+(133444517/200000000 : ℝ)*X 2 0+(3872291397/10000000000 : ℝ)*X 2 1+(2164091243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-6052725679/10000000000 : ℝ)*X 0 0+(2573520619/10000000000 : ℝ)*X 0 1+(849274411/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((744692887/5000000000 : ℝ)*X 1 0+(-596340533/2500000000 : ℝ)*X 1 1+(8216793557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4155588211/5000000000 : ℝ)*X 2 0+(1580446891/5000000000 : ℝ)*X 2 1+(18319267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((84377673/400000000 : ℝ)*X 0 0+(1894592717/2500000000 : ℝ)*X 0 1+(2755151387/10000000000 : ℝ)*X 0 2+(84377673/400000000 : ℝ)*X 1 0+(1894592717/2500000000 : ℝ)*X 1 1+(2755151387/10000000000 : ℝ)*X 1 2+(84377673/400000000 : ℝ)*X 2 0+(1894592717/2500000000 : ℝ)*X 2 1+(2755151387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((84819/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84819/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (49236382384556835682256508819/10369274398000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423755842329/500000000000 : ℝ)*(base7) + (255573/1000000000000 : ℝ)*(base39) + (84891/125000000000 : ℝ)*(base50) + (1655153/500000000000 : ℝ)*(base53) + (331759/1000000000000 : ℝ)*(base60) + (1737164728239/1000000000000 : ℝ)*(major_s3_0) + (1737164728239/1000000000000 : ℝ)*(major_s3_1) + (1737161417933/1000000000000 : ℝ)*(major_s3_2) + (1473641/1000000000000 : ℝ)*(sp_s3_0) + (222238604501/125000000000 : ℝ)*(sp_s3_7) + (888972606783/500000000000 : ℝ)*(sp_s3_8) + (55560891371/31250000000 : ℝ)*(sp_s3_9) + (2021874687443/1000000000000 : ℝ)*(sp_s3_13) + (34903917/1000000000000 : ℝ)*(sp_s3_14) + (36698843837/31250000000 : ℝ)*(f.failure) + (55560891371/31250000000 : ℝ)*(f.sum) + (83753254837046548129/179123742000000000000000000000000 : ℝ)*base63 + (351001438463819/877000000000000000000000000 : ℝ)*base64 + (6998350206637341/9077600000000000000000000000 : ℝ)*base66 + (486272881722709/7893000000000000000000000000 : ℝ)*base68 + (4524182350497912601/13250593000000000000000000000000 : ℝ)*base70 + (9057736884449/47215625000000000000000000 : ℝ)*base72 + (60068679536807/181552000000000000000000000 : ℝ)*base75 + (856608531906799/1510900000000000000000000000 : ℝ)*base76 + (49945586571327494737/137153458400000000000000000000000 : ℝ)*base78 + (2487/3125000000000000 : ℝ)*base86 + (2487/3125000000000000 : ℝ)*base88 + (2487/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16909/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16909/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (92505242489365340718469517/9951319000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47780613871/250000000000 : ℝ)*(base5) + (84665592273/100000000000 : ℝ)*(base7) + (479481/200000000000 : ℝ)*(base33) + (26265400107/250000000000 : ℝ)*(base60) + (1935942858071/1000000000000 : ℝ)*(major_s3_0) + (1935945255477/1000000000000 : ℝ)*(major_s3_1) + (1935945255477/1000000000000 : ℝ)*(major_s3_2) + (1392453/250000000000 : ℝ)*(sp_s3_0) + (593063/200000000000 : ℝ)*(sp_s3_1) + (50531269/1000000000000 : ℝ)*(sp_s3_8) + (2041649417623/1000000000000 : ℝ)*(sp_s3_14) + (1020799546723/500000000000 : ℝ)*(sp_s3_15) + (1116387522757/500000000000 : ℝ)*(sp_s3_16) + (982138321559/500000000000 : ℝ)*(sp_s3_20) + (20449112123/15625000000 : ℝ)*(f.failure) + (510413746859/250000000000 : ℝ)*(f.sum) + (12057792290905563883/59707914000000000000000000000000 : ℝ)*base62 + (287540779017589/877000000000000000000000000 : ℝ)*base65 + (6740619885106257/9077600000000000000000000000 : ℝ)*base67 + (1529809091930807/2631000000000000000000000000 : ℝ)*base68 + (3164914905696511369/13250593000000000000000000000000 : ℝ)*base70 + (376255592011299/755450000000000000000000000 : ℝ)*base73 + (13738045052979/181552000000000000000000000 : ℝ)*base74 + (534607148932149/1510900000000000000000000000 : ℝ)*base77 + (2064731564669644939/137153458400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (701/781250000000000 : ℝ)*base87 + (321/3125000000000000 : ℝ)*base88 + (321/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13693/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13693/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2185903143520924643820323737753/225531718156500000000000000000000000 : ℝ) := by norm_num
    linear_combination (13469606321/250000000000 : ℝ)*(base5) + (443553880747/1000000000000 : ℝ)*(base7) + (71801201767/500000000000 : ℝ)*(base33) + (134707797913/200000000000 : ℝ)*(base44) + (18580684307/500000000000 : ℝ)*(base50) + (380223434887/250000000000 : ℝ)*(major_s3_0) + (247739288379/250000000000 : ℝ)*(major_s3_1) + (1664496143081/1000000000000 : ℝ)*(major_s3_2) + (6618293/50000000000 : ℝ)*(sp_s3_1) + (13037903/125000000000 : ℝ)*(sp_s3_16) + (1930549097373/1000000000000 : ℝ)*(sp_s3_21) + (556637669207/500000000000 : ℝ)*(sp_s3_22) + (1840720815899/1000000000000 : ℝ)*(sp_s3_23) + (168274769327/200000000000 : ℝ)*(sp_s3_27) + (1125237380737/1000000000000 : ℝ)*(f.failure) + (1930549097373/1000000000000 : ℝ)*(f.sum) + (34874077463586698339/89561871000000000000000000000000 : ℝ)*base63 + (340103003116783/877000000000000000000000000 : ℝ)*base64 + (1792922387592081/2269400000000000000000000000 : ℝ)*base66 + (4921271530053587/7893000000000000000000000000 : ℝ)*base69 + (89433964780371207/13250593000000000000000000000000 : ℝ)*base70 + (32974058862777/755450000000000000000000000 : ℝ)*base73 + (217655740576929/226940000000000000000000000 : ℝ)*base75 + (53419447685311/188862500000000000000000000 : ℝ)*base76 + (15117523485418461833/34288364600000000000000000000000 : ℝ)*base78 + (15003/25000000000000000 : ℝ)*base86 + (9997/25000000000000000 : ℝ)*base89 + (9997/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((45327/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45327/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11347/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11347/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7893/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7893/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((84819/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84819/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16909/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16909/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13693/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13693/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301059_s3 p hpa hpb X hX hprev2

#print axioms solution
