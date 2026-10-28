-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:58:52.044372+00:00
-- url     : https://prove2.me/submissions/5a91a936-ed95-4324-8b51-d40bd5d9559d

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
theorem collision_support_c303062_s2_s2_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-81581057/625000000 : ℝ)*x 0 + (39187061/78125000 : ℝ)*x 1 + (-6179570649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81581057/625000000 : ℝ)^33 ≤ (850445138691/12500000000000 : ℝ)^25 := by
    have hnat : (81581057 : ℕ)^33*12500000000000^25 ≤ 850445138691^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81581057 625000000 850445138691 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39187061/78125000 : ℝ)^33 ≤ (40222171610293/100000000000000 : ℝ)^25 := by
    have hnat : (39187061 : ℕ)^33*100000000000000^25 ≤ 40222171610293^25*78125000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39187061 78125000 40222171610293 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6179570649/10000000000 : ℝ)^33 ≤ (52974267265297/100000000000000 : ℝ)^25 := by
    have hnat : (6179570649 : ℕ)^33*100000000000000^25 ≤ 52974267265297^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6179570649 10000000000 52974267265297 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81581057/625000000 : ℝ), (39187061/78125000 : ℝ), (-6179570649/10000000000 : ℝ)] ![(850445138691/12500000000000 : ℝ), (40222171610293/100000000000000 : ℝ), (52974267265297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81581057/625000000 : ℝ)|^33 ≤ (850445138691/12500000000000 : ℝ)^25
        have hw : |(-81581057/625000000 : ℝ)|=(81581057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39187061/78125000 : ℝ)|^33 ≤ (40222171610293/100000000000000 : ℝ)^25
        have hw : |(39187061/78125000 : ℝ)|=(39187061/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6179570649/10000000000 : ℝ)|^33 ≤ (52974267265297/100000000000000 : ℝ)^25
        have hw : |(-6179570649/10000000000 : ℝ)|=(6179570649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2512645083/5000000000 : ℝ)*x 0 + (-1301889259/10000000000 : ℝ)*x 1 + (-1234579039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2512645083/5000000000 : ℝ)^33 ≤ (40321131362423/100000000000000 : ℝ)^25 := by
    have hnat : (2512645083 : ℕ)^33*100000000000000^25 ≤ 40321131362423^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512645083 5000000000 40321131362423 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301889259/10000000000 : ℝ)^33 ≤ (105939462227/1562500000000 : ℝ)^25 := by
    have hnat : (1301889259 : ℕ)^33*1562500000000^25 ≤ 105939462227^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301889259 10000000000 105939462227 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1234579039/2000000000 : ℝ)^33 ≤ (528987430351/1000000000000 : ℝ)^25 := by
    have hnat : (1234579039 : ℕ)^33*1000000000000^25 ≤ 528987430351^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234579039 2000000000 528987430351 1000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2512645083/5000000000 : ℝ), (-1301889259/10000000000 : ℝ), (-1234579039/2000000000 : ℝ)] ![(40321131362423/100000000000000 : ℝ), (105939462227/1562500000000 : ℝ), (528987430351/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2512645083/5000000000 : ℝ)|^33 ≤ (40321131362423/100000000000000 : ℝ)^25
        have hw : |(2512645083/5000000000 : ℝ)|=(2512645083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1301889259/10000000000 : ℝ)|^33 ≤ (105939462227/1562500000000 : ℝ)^25
        have hw : |(-1301889259/10000000000 : ℝ)|=(1301889259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1234579039/2000000000 : ℝ)|^33 ≤ (528987430351/1000000000000 : ℝ)^25
        have hw : |(-1234579039/2000000000 : ℝ)|=(1234579039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (134860477/250000000 : ℝ)*x 0 + (5479206633/10000000000 : ℝ)*x 1 + (454227619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134860477/250000000 : ℝ)^33 ≤ (8855171504761/20000000000000 : ℝ)^25 := by
    have hnat : (134860477 : ℕ)^33*20000000000000^25 ≤ 8855171504761^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134860477 250000000 8855171504761 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479206633/10000000000 : ℝ)^33 ≤ (225983817359/500000000000 : ℝ)^25 := by
    have hnat : (5479206633 : ℕ)^33*500000000000^25 ≤ 225983817359^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479206633 10000000000 225983817359 500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454227619/2500000000 : ℝ)^33 ≤ (10527378996647/100000000000000 : ℝ)^25 := by
    have hnat : (454227619 : ℕ)^33*100000000000000^25 ≤ 10527378996647^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454227619 2500000000 10527378996647 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134860477/250000000 : ℝ), (5479206633/10000000000 : ℝ), (454227619/2500000000 : ℝ)] ![(8855171504761/20000000000000 : ℝ), (225983817359/500000000000 : ℝ), (10527378996647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134860477/250000000 : ℝ)|^33 ≤ (8855171504761/20000000000000 : ℝ)^25
        have hw : |(134860477/250000000 : ℝ)|=(134860477/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479206633/10000000000 : ℝ)|^33 ≤ (225983817359/500000000000 : ℝ)^25
        have hw : |(5479206633/10000000000 : ℝ)|=(5479206633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(454227619/2500000000 : ℝ)|^33 ≤ (10527378996647/100000000000000 : ℝ)^25
        have hw : |(454227619/2500000000 : ℝ)|=(454227619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-198253969/1250000000 : ℝ)*x 0 + (2709009443/10000000000 : ℝ)*x 1 + (-7908558771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198253969/1250000000 : ℝ)^33 ≤ (8798561588269/100000000000000 : ℝ)^25 := by
    have hnat : (198253969 : ℕ)^33*100000000000000^25 ≤ 8798561588269^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198253969 1250000000 8798561588269 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709009443/10000000000 : ℝ)^33 ≤ (2229563766839/12500000000000 : ℝ)^25 := by
    have hnat : (2709009443 : ℕ)^33*12500000000000^25 ≤ 2229563766839^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709009443 10000000000 2229563766839 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7908558771/10000000000 : ℝ)^33 ≤ (18341232064219/25000000000000 : ℝ)^25 := by
    have hnat : (7908558771 : ℕ)^33*25000000000000^25 ≤ 18341232064219^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7908558771 10000000000 18341232064219 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198253969/1250000000 : ℝ), (2709009443/10000000000 : ℝ), (-7908558771/10000000000 : ℝ)] ![(8798561588269/100000000000000 : ℝ), (2229563766839/12500000000000 : ℝ), (18341232064219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198253969/1250000000 : ℝ)|^33 ≤ (8798561588269/100000000000000 : ℝ)^25
        have hw : |(-198253969/1250000000 : ℝ)|=(198253969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709009443/10000000000 : ℝ)|^33 ≤ (2229563766839/12500000000000 : ℝ)^25
        have hw : |(2709009443/10000000000 : ℝ)|=(2709009443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7908558771/10000000000 : ℝ)|^33 ≤ (18341232064219/25000000000000 : ℝ)^25
        have hw : |(-7908558771/10000000000 : ℝ)|=(7908558771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3142031371/10000000000 : ℝ)*x 0 + (-130003419/1250000000 : ℝ)*x 1 + (-1975125567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3142031371/10000000000 : ℝ)^33 ≤ (10846456693307/50000000000000 : ℝ)^25 := by
    have hnat : (3142031371 : ℕ)^33*50000000000000^25 ≤ 10846456693307^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3142031371 10000000000 10846456693307 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130003419/1250000000 : ℝ)^33 ≤ (5040795566599/100000000000000 : ℝ)^25 := by
    have hnat : (130003419 : ℕ)^33*100000000000000^25 ≤ 5040795566599^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130003419 1250000000 5040795566599 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1975125567/2500000000 : ℝ)^33 ≤ (73266291031767/100000000000000 : ℝ)^25 := by
    have hnat : (1975125567 : ℕ)^33*100000000000000^25 ≤ 73266291031767^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975125567 2500000000 73266291031767 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3142031371/10000000000 : ℝ), (-130003419/1250000000 : ℝ), (-1975125567/2500000000 : ℝ)] ![(10846456693307/50000000000000 : ℝ), (5040795566599/100000000000000 : ℝ), (73266291031767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3142031371/10000000000 : ℝ)|^33 ≤ (10846456693307/50000000000000 : ℝ)^25
        have hw : |(3142031371/10000000000 : ℝ)|=(3142031371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130003419/1250000000 : ℝ)|^33 ≤ (5040795566599/100000000000000 : ℝ)^25
        have hw : |(-130003419/1250000000 : ℝ)|=(130003419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1975125567/2500000000 : ℝ)|^33 ≤ (73266291031767/100000000000000 : ℝ)^25
        have hw : |(-1975125567/2500000000 : ℝ)|=(1975125567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (35593849/100000000 : ℝ)*x 0 + (3585573131/5000000000 : ℝ)*x 1 + (1741194283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35593849/100000000 : ℝ)^33 ≤ (1022998342871/4000000000000 : ℝ)^25 := by
    have hnat : (35593849 : ℕ)^33*4000000000000^25 ≤ 1022998342871^25*100000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35593849 100000000 1022998342871 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3585573131/5000000000 : ℝ)^33 ≤ (32236429281553/50000000000000 : ℝ)^25 := by
    have hnat : (3585573131 : ℕ)^33*50000000000000^25 ≤ 32236429281553^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3585573131 5000000000 32236429281553 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1741194283/10000000000 : ℝ)^33 ≤ (1990436571359/20000000000000 : ℝ)^25 := by
    have hnat : (1741194283 : ℕ)^33*20000000000000^25 ≤ 1990436571359^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741194283 10000000000 1990436571359 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35593849/100000000 : ℝ), (3585573131/5000000000 : ℝ), (1741194283/10000000000 : ℝ)] ![(1022998342871/4000000000000 : ℝ), (32236429281553/50000000000000 : ℝ), (1990436571359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35593849/100000000 : ℝ)|^33 ≤ (1022998342871/4000000000000 : ℝ)^25
        have hw : |(35593849/100000000 : ℝ)|=(35593849/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3585573131/5000000000 : ℝ)|^33 ≤ (32236429281553/50000000000000 : ℝ)^25
        have hw : |(3585573131/5000000000 : ℝ)|=(3585573131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1741194283/10000000000 : ℝ)|^33 ≤ (1990436571359/20000000000000 : ℝ)^25
        have hw : |(1741194283/10000000000 : ℝ)|=(1741194283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1988996843/5000000000 : ℝ)*x 0 + (3831748917/5000000000 : ℝ)*x 1 + (-3597093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988996843/5000000000 : ℝ)^33 ≤ (18511287053/62500000000 : ℝ)^25 := by
    have hnat : (1988996843 : ℕ)^33*62500000000^25 ≤ 18511287053^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988996843 5000000000 18511287053 62500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3831748917/5000000000 : ℝ)^33 ≤ (70379097186823/100000000000000 : ℝ)^25 := by
    have hnat : (3831748917 : ℕ)^33*100000000000000^25 ≤ 70379097186823^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3831748917 5000000000 70379097186823 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3597093/10000000000 : ℝ)^33 ≤ (1421759713/50000000000000 : ℝ)^25 := by
    have hnat : (3597093 : ℕ)^33*50000000000000^25 ≤ 1421759713^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3597093 10000000000 1421759713 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1988996843/5000000000 : ℝ), (3831748917/5000000000 : ℝ), (-3597093/10000000000 : ℝ)] ![(18511287053/62500000000 : ℝ), (70379097186823/100000000000000 : ℝ), (1421759713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1988996843/5000000000 : ℝ)|^33 ≤ (18511287053/62500000000 : ℝ)^25
        have hw : |(1988996843/5000000000 : ℝ)|=(1988996843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3831748917/5000000000 : ℝ)|^33 ≤ (70379097186823/100000000000000 : ℝ)^25
        have hw : |(3831748917/5000000000 : ℝ)|=(3831748917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3597093/10000000000 : ℝ)|^33 ≤ (1421759713/50000000000000 : ℝ)^25
        have hw : |(-3597093/10000000000 : ℝ)|=(3597093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029808733/10000000000 : ℝ)*x 0 + (3104573127/10000000000 : ℝ)*x 1 + (-3966823099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029808733/10000000000 : ℝ)^33 ≤ (2487761126453/50000000000000 : ℝ)^25 := by
    have hnat : (1029808733 : ℕ)^33*50000000000000^25 ≤ 2487761126453^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029808733 10000000000 2487761126453 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104573127/10000000000 : ℝ)^33 ≤ (21352193671789/100000000000000 : ℝ)^25 := by
    have hnat : (3104573127 : ℕ)^33*100000000000000^25 ≤ 21352193671789^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104573127 10000000000 21352193671789 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3966823099/5000000000 : ℝ)^33 ≤ (18418071014727/25000000000000 : ℝ)^25 := by
    have hnat : (3966823099 : ℕ)^33*25000000000000^25 ≤ 18418071014727^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3966823099 5000000000 18418071014727 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029808733/10000000000 : ℝ), (3104573127/10000000000 : ℝ), (-3966823099/5000000000 : ℝ)] ![(2487761126453/50000000000000 : ℝ), (21352193671789/100000000000000 : ℝ), (18418071014727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029808733/10000000000 : ℝ)|^33 ≤ (2487761126453/50000000000000 : ℝ)^25
        have hw : |(-1029808733/10000000000 : ℝ)|=(1029808733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104573127/10000000000 : ℝ)|^33 ≤ (21352193671789/100000000000000 : ℝ)^25
        have hw : |(3104573127/10000000000 : ℝ)|=(3104573127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3966823099/5000000000 : ℝ)|^33 ≤ (18418071014727/25000000000000 : ℝ)^25
        have hw : |(-3966823099/5000000000 : ℝ)|=(3966823099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (537785009/2000000000 : ℝ)*x 0 + (-1581393671/10000000000 : ℝ)*x 1 + (-7925563301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537785009/2000000000 : ℝ)^33 ≤ (8831081308491/50000000000000 : ℝ)^25 := by
    have hnat : (537785009 : ℕ)^33*50000000000000^25 ≤ 8831081308491^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537785009 2000000000 8831081308491 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1581393671/10000000000 : ℝ)^33 ≤ (4382307009811/50000000000000 : ℝ)^25 := by
    have hnat : (1581393671 : ℕ)^33*50000000000000^25 ≤ 4382307009811^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581393671 10000000000 4382307009811 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7925563301/10000000000 : ℝ)^33 ≤ (4598326458903/6250000000000 : ℝ)^25 := by
    have hnat : (7925563301 : ℕ)^33*6250000000000^25 ≤ 4598326458903^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7925563301 10000000000 4598326458903 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537785009/2000000000 : ℝ), (-1581393671/10000000000 : ℝ), (-7925563301/10000000000 : ℝ)] ![(8831081308491/50000000000000 : ℝ), (4382307009811/50000000000000 : ℝ), (4598326458903/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537785009/2000000000 : ℝ)|^33 ≤ (8831081308491/50000000000000 : ℝ)^25
        have hw : |(537785009/2000000000 : ℝ)|=(537785009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1581393671/10000000000 : ℝ)|^33 ≤ (4382307009811/50000000000000 : ℝ)^25
        have hw : |(-1581393671/10000000000 : ℝ)|=(1581393671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7925563301/10000000000 : ℝ)|^33 ≤ (4598326458903/6250000000000 : ℝ)^25
        have hw : |(-7925563301/10000000000 : ℝ)|=(7925563301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3540805391/5000000000 : ℝ)*x 0 + (3665449879/10000000000 : ℝ)*x 1 + (873889141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3540805391/5000000000 : ℝ)^33 ≤ (63412417541311/100000000000000 : ℝ)^25 := by
    have hnat : (3540805391 : ℕ)^33*100000000000000^25 ≤ 63412417541311^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3540805391 5000000000 63412417541311 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665449879/10000000000 : ℝ)^33 ≤ (5317138983267/20000000000000 : ℝ)^25 := by
    have hnat : (3665449879 : ℕ)^33*20000000000000^25 ≤ 5317138983267^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665449879 10000000000 5317138983267 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873889141/5000000000 : ℝ)^33 ≤ (625117970821/6250000000000 : ℝ)^25 := by
    have hnat : (873889141 : ℕ)^33*6250000000000^25 ≤ 625117970821^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873889141 5000000000 625117970821 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3540805391/5000000000 : ℝ), (3665449879/10000000000 : ℝ), (873889141/5000000000 : ℝ)] ![(63412417541311/100000000000000 : ℝ), (5317138983267/20000000000000 : ℝ), (625117970821/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3540805391/5000000000 : ℝ)|^33 ≤ (63412417541311/100000000000000 : ℝ)^25
        have hw : |(3540805391/5000000000 : ℝ)|=(3540805391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3665449879/10000000000 : ℝ)|^33 ≤ (5317138983267/20000000000000 : ℝ)^25
        have hw : |(3665449879/10000000000 : ℝ)|=(3665449879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(873889141/5000000000 : ℝ)|^33 ≤ (625117970821/6250000000000 : ℝ)^25
        have hw : |(873889141/5000000000 : ℝ)|=(873889141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1558884223/2000000000 : ℝ)*x 0 + (238429867/625000000 : ℝ)*x 1 + (-4570067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1558884223/2000000000 : ℝ)^33 ≤ (8996316297179/12500000000000 : ℝ)^25 := by
    have hnat : (1558884223 : ℕ)^33*12500000000000^25 ≤ 8996316297179^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558884223 2000000000 8996316297179 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238429867/625000000 : ℝ)^33 ≤ (875799041191/3125000000000 : ℝ)^25 := by
    have hnat : (238429867 : ℕ)^33*3125000000000^25 ≤ 875799041191^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238429867 625000000 875799041191 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4570067/10000000000 : ℝ)^33 ≤ (780059597/20000000000000 : ℝ)^25 := by
    have hnat : (4570067 : ℕ)^33*20000000000000^25 ≤ 780059597^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570067 10000000000 780059597 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1558884223/2000000000 : ℝ), (238429867/625000000 : ℝ), (-4570067/10000000000 : ℝ)] ![(8996316297179/12500000000000 : ℝ), (875799041191/3125000000000 : ℝ), (780059597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1558884223/2000000000 : ℝ)|^33 ≤ (8996316297179/12500000000000 : ℝ)^25
        have hw : |(1558884223/2000000000 : ℝ)|=(1558884223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238429867/625000000 : ℝ)|^33 ≤ (875799041191/3125000000000 : ℝ)^25
        have hw : |(238429867/625000000 : ℝ)|=(238429867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4570067/10000000000 : ℝ)|^33 ≤ (780059597/20000000000000 : ℝ)^25
        have hw : |(-4570067/10000000000 : ℝ)|=(4570067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-16329459/400000000 : ℝ)*x 0 + (3279848337/5000000000 : ℝ)*x 1 + (-1021905293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16329459/400000000 : ℝ)^33 ≤ (733455192279/50000000000000 : ℝ)^25 := by
    have hnat : (16329459 : ℕ)^33*50000000000000^25 ≤ 733455192279^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16329459 400000000 733455192279 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3279848337/5000000000 : ℝ)^33 ≤ (28658705160621/50000000000000 : ℝ)^25 := by
    have hnat : (3279848337 : ℕ)^33*50000000000000^25 ≤ 28658705160621^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3279848337 5000000000 28658705160621 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021905293/2000000000 : ℝ)^33 ≤ (41215679278861/100000000000000 : ℝ)^25 := by
    have hnat : (1021905293 : ℕ)^33*100000000000000^25 ≤ 41215679278861^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021905293 2000000000 41215679278861 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16329459/400000000 : ℝ), (3279848337/5000000000 : ℝ), (-1021905293/2000000000 : ℝ)] ![(733455192279/50000000000000 : ℝ), (28658705160621/50000000000000 : ℝ), (41215679278861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16329459/400000000 : ℝ)|^33 ≤ (733455192279/50000000000000 : ℝ)^25
        have hw : |(-16329459/400000000 : ℝ)|=(16329459/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3279848337/5000000000 : ℝ)|^33 ≤ (28658705160621/50000000000000 : ℝ)^25
        have hw : |(3279848337/5000000000 : ℝ)|=(3279848337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021905293/2000000000 : ℝ)|^33 ≤ (41215679278861/100000000000000 : ℝ)^25
        have hw : |(-1021905293/2000000000 : ℝ)|=(1021905293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6828238811/10000000000 : ℝ)*x 0 + (-165548011/2500000000 : ℝ)*x 1 + (-4687958853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6828238811/10000000000 : ℝ)^33 ≤ (6043485525571/10000000000000 : ℝ)^25 := by
    have hnat : (6828238811 : ℕ)^33*10000000000000^25 ≤ 6043485525571^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6828238811 10000000000 6043485525571 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165548011/2500000000 : ℝ)^33 ≤ (1388893129681/50000000000000 : ℝ)^25 := by
    have hnat : (165548011 : ℕ)^33*50000000000000^25 ≤ 1388893129681^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165548011 2500000000 1388893129681 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4687958853/10000000000 : ℝ)^33 ≤ (9196839618483/25000000000000 : ℝ)^25 := by
    have hnat : (4687958853 : ℕ)^33*25000000000000^25 ≤ 9196839618483^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4687958853 10000000000 9196839618483 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6828238811/10000000000 : ℝ), (-165548011/2500000000 : ℝ), (-4687958853/10000000000 : ℝ)] ![(6043485525571/10000000000000 : ℝ), (1388893129681/50000000000000 : ℝ), (9196839618483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6828238811/10000000000 : ℝ)|^33 ≤ (6043485525571/10000000000000 : ℝ)^25
        have hw : |(6828238811/10000000000 : ℝ)|=(6828238811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-165548011/2500000000 : ℝ)|^33 ≤ (1388893129681/50000000000000 : ℝ)^25
        have hw : |(-165548011/2500000000 : ℝ)|=(165548011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4687958853/10000000000 : ℝ)|^33 ≤ (9196839618483/25000000000000 : ℝ)^25
        have hw : |(-4687958853/10000000000 : ℝ)|=(4687958853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3323934807/10000000000 : ℝ)*x 0 + (221539051/312500000 : ℝ)*x 1 + (8592407/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3323934807/10000000000 : ℝ)^33 ≤ (11682917254291/50000000000000 : ℝ)^25 := by
    have hnat : (3323934807 : ℕ)^33*50000000000000^25 ≤ 11682917254291^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3323934807 10000000000 11682917254291 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221539051/312500000 : ℝ)^33 ≤ (3175136203/5000000000 : ℝ)^25 := by
    have hnat : (221539051 : ℕ)^33*5000000000^25 ≤ 3175136203^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221539051 312500000 3175136203 5000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8592407/40000000 : ℝ)^33 ≤ (6565720709457/50000000000000 : ℝ)^25 := by
    have hnat : (8592407 : ℕ)^33*50000000000000^25 ≤ 6565720709457^25*40000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8592407 40000000 6565720709457 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3323934807/10000000000 : ℝ), (221539051/312500000 : ℝ), (8592407/40000000 : ℝ)] ![(11682917254291/50000000000000 : ℝ), (3175136203/5000000000 : ℝ), (6565720709457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3323934807/10000000000 : ℝ)|^33 ≤ (11682917254291/50000000000000 : ℝ)^25
        have hw : |(3323934807/10000000000 : ℝ)|=(3323934807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221539051/312500000 : ℝ)|^33 ≤ (3175136203/5000000000 : ℝ)^25
        have hw : |(221539051/312500000 : ℝ)|=(221539051/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8592407/40000000 : ℝ)|^33 ≤ (6565720709457/50000000000000 : ℝ)^25
        have hw : |(8592407/40000000 : ℝ)|=(8592407/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s2_s2_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (827337859/1000000000 : ℝ)*x 0 + (3158678939/10000000000 : ℝ)*x 1 + (-3740019/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827337859/1000000000 : ℝ)^33 ≤ (19466211343503/25000000000000 : ℝ)^25 := by
    have hnat : (827337859 : ℕ)^33*25000000000000^25 ≤ 19466211343503^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827337859 1000000000 19466211343503 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3158678939/10000000000 : ℝ)^33 ≤ (21844758095791/100000000000000 : ℝ)^25 := by
    have hnat : (3158678939 : ℕ)^33*100000000000000^25 ≤ 21844758095791^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3158678939 10000000000 21844758095791 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3740019/312500000 : ℝ)^33 ≤ (7259912849/2500000000000 : ℝ)^25 := by
    have hnat : (3740019 : ℕ)^33*2500000000000^25 ≤ 7259912849^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3740019 312500000 7259912849 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827337859/1000000000 : ℝ), (3158678939/10000000000 : ℝ), (-3740019/312500000 : ℝ)] ![(19466211343503/25000000000000 : ℝ), (21844758095791/100000000000000 : ℝ), (7259912849/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827337859/1000000000 : ℝ)|^33 ≤ (19466211343503/25000000000000 : ℝ)^25
        have hw : |(827337859/1000000000 : ℝ)|=(827337859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3158678939/10000000000 : ℝ)|^33 ≤ (21844758095791/100000000000000 : ℝ)^25
        have hw : |(3158678939/10000000000 : ℝ)|=(3158678939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3740019/312500000 : ℝ)|^33 ≤ (7259912849/2500000000000 : ℝ)^25
        have hw : |(-3740019/312500000 : ℝ)|=(3740019/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303062_s2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((86563/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86563/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43049/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43049/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-71347/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-71347/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((75133/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75133/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9387/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9387/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29253/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29253/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91389/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (86563/100000 : ℝ) ^ (131/32 : ℝ) ≤ (3462056232196103009/6250000000000000000 : ℝ) := by
    have hpowers : (86563/100000 : ℝ)^131 ≤ (3462056232196103009/6250000000000000000 : ℝ)^32 := by
      have hnat : (86563 : ℕ)^131*6250000000000000000^32 ≤ 3462056232196103009^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86563 100000 3462056232196103009 6250000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (86563/100000 : ℝ)) (X := (3462056232196103009/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (9712056232196103009/6250000000000000000 : ℝ) ≤ (11136835703011713/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (9712056232196103009/6250000000000000000 : ℝ)^32 ≤ (11136835703011713/10000000000000000 : ℝ)^131 := by
      have hnat : (9712056232196103009 : ℕ)^32*10000000000000000^131 ≤ 11136835703011713^131*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9712056232196103009 6250000000000000000 11136835703011713 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11136835703011713/10000000000000000 : ℝ)) (X := (9712056232196103009/6250000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (6587056232196103009/3125000000000000000 : ℝ) ≤ (11997928894923041/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (6587056232196103009/3125000000000000000 : ℝ)^32 ≤ (11997928894923041/10000000000000000 : ℝ)^131 := by
      have hnat : (6587056232196103009 : ℕ)^32*10000000000000000^131 ≤ 11997928894923041^131*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6587056232196103009 3125000000000000000 11997928894923041 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11997928894923041/10000000000000000 : ℝ)) (X := (6587056232196103009/3125000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1136835703011713/8656300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(26909162247229/270509375000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (86563/100000 : ℝ)) (alpha := (1136835703011713/8656300000000000 : ℝ)) (beta := (26909162247229/270509375000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (86563/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1136835703011713/8656300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(26909162247229/270509375000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (43049/50000 : ℝ) ^ (131/32 : ℝ) ≤ (13546211782849887263/25000000000000000000 : ℝ) := by
    have hpowers : (43049/50000 : ℝ)^131 ≤ (13546211782849887263/25000000000000000000 : ℝ)^32 := by
      have hnat : (43049 : ℕ)^131*25000000000000000000^32 ≤ 13546211782849887263^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43049 50000 13546211782849887263 25000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43049/50000 : ℝ)) (X := (13546211782849887263/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (38546211782849887263/25000000000000000000 : ℝ) ≤ (11115624031989227/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (38546211782849887263/25000000000000000000 : ℝ)^32 ≤ (11115624031989227/10000000000000000 : ℝ)^131 := by
      have hnat : (38546211782849887263 : ℕ)^32*10000000000000000^131 ≤ 11115624031989227^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38546211782849887263 25000000000000000000 11115624031989227 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11115624031989227/10000000000000000 : ℝ)) (X := (38546211782849887263/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (26046211782849887263/12500000000000000000 : ℝ) ≤ (2392837716956211/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (26046211782849887263/12500000000000000000 : ℝ)^32 ≤ (2392837716956211/2000000000000000 : ℝ)^131 := by
      have hnat : (26046211782849887263 : ℕ)^32*2000000000000000^131 ≤ 2392837716956211^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26046211782849887263 12500000000000000000 2392837716956211 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2392837716956211/2000000000000000 : ℝ)) (X := (26046211782849887263/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1115624031989227/8609800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(212141138197957/2152450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (43049/50000 : ℝ)) (alpha := (1115624031989227/8609800000000000 : ℝ)) (beta := (212141138197957/2152450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (43049/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1115624031989227/8609800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(212141138197957/2152450000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (71347/100000 : ℝ) ^ (131/32 : ℝ) ≤ (6276201069532452869/25000000000000000000 : ℝ) := by
    have hpowers : (71347/100000 : ℝ)^131 ≤ (6276201069532452869/25000000000000000000 : ℝ)^32 := by
      have hnat : (71347 : ℕ)^131*25000000000000000000^32 ≤ 6276201069532452869^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71347 100000 6276201069532452869 25000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71347/100000 : ℝ)) (X := (6276201069532452869/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (31276201069532452869/25000000000000000000 : ℝ) ≤ (2112475011960927/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (31276201069532452869/25000000000000000000 : ℝ)^32 ≤ (2112475011960927/2000000000000000 : ℝ)^131 := by
      have hnat : (31276201069532452869 : ℕ)^32*2000000000000000^131 ≤ 2112475011960927^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31276201069532452869 25000000000000000000 2112475011960927 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2112475011960927/2000000000000000 : ℝ)) (X := (31276201069532452869/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (18776201069532452869/12500000000000000000 : ℝ) ≤ (11044925744910087/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (18776201069532452869/12500000000000000000 : ℝ)^32 ≤ (11044925744910087/10000000000000000 : ℝ)^131 := by
      have hnat : (18776201069532452869 : ℕ)^32*10000000000000000^131 ≤ 11044925744910087^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18776201069532452869 12500000000000000000 11044925744910087 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11044925744910087/10000000000000000 : ℝ)) (X := (18776201069532452869/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(112475011960927/1426940000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(120637671276363/1783675000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (71347/100000 : ℝ)) (alpha := (112475011960927/1426940000000000 : ℝ)) (beta := (120637671276363/1783675000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (71347/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(112475011960927/1426940000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(120637671276363/1783675000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-81581057/625000000 : ℝ)*X 0 0+(39187061/78125000 : ℝ)*X 0 1+(-6179570649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2512645083/5000000000 : ℝ)*X 1 0+(-1301889259/10000000000 : ℝ)*X 1 1+(-1234579039/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((134860477/250000000 : ℝ)*X 2 0+(5479206633/10000000000 : ℝ)*X 2 1+(454227619/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-198253969/1250000000 : ℝ)*X 0 0+(2709009443/10000000000 : ℝ)*X 0 1+(-7908558771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((3142031371/10000000000 : ℝ)*X 1 0+(-130003419/1250000000 : ℝ)*X 1 1+(-1975125567/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((35593849/100000000 : ℝ)*X 2 0+(3585573131/5000000000 : ℝ)*X 2 1+(1741194283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1988996843/5000000000 : ℝ)*X 0 0+(3831748917/5000000000 : ℝ)*X 0 1+(-3597093/10000000000 : ℝ)*X 0 2+(1988996843/5000000000 : ℝ)*X 1 0+(3831748917/5000000000 : ℝ)*X 1 1+(-3597093/10000000000 : ℝ)*X 1 2+(1988996843/5000000000 : ℝ)*X 2 0+(3831748917/5000000000 : ℝ)*X 2 1+(-3597093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1029808733/10000000000 : ℝ)*X 0 0+(3104573127/10000000000 : ℝ)*X 0 1+(-3966823099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((537785009/2000000000 : ℝ)*X 1 0+(-1581393671/10000000000 : ℝ)*X 1 1+(-7925563301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3540805391/5000000000 : ℝ)*X 2 0+(3665449879/10000000000 : ℝ)*X 2 1+(873889141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1558884223/2000000000 : ℝ)*X 0 0+(238429867/625000000 : ℝ)*X 0 1+(-4570067/10000000000 : ℝ)*X 0 2+(1558884223/2000000000 : ℝ)*X 1 0+(238429867/625000000 : ℝ)*X 1 1+(-4570067/10000000000 : ℝ)*X 1 2+(1558884223/2000000000 : ℝ)*X 2 0+(238429867/625000000 : ℝ)*X 2 1+(-4570067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-16329459/400000000 : ℝ)*X 0 0+(3279848337/5000000000 : ℝ)*X 0 1+(-1021905293/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((6828238811/10000000000 : ℝ)*X 1 0+(-165548011/2500000000 : ℝ)*X 1 1+(-4687958853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3323934807/10000000000 : ℝ)*X 2 0+(221539051/312500000 : ℝ)*X 2 1+(8592407/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((827337859/1000000000 : ℝ)*X 0 0+(3158678939/10000000000 : ℝ)*X 0 1+(-3740019/312500000 : ℝ)*X 0 2+(827337859/1000000000 : ℝ)*X 1 0+(3158678939/10000000000 : ℝ)*X 1 1+(-3740019/312500000 : ℝ)*X 1 2+(827337859/1000000000 : ℝ)*X 2 0+(3158678939/10000000000 : ℝ)*X 2 1+(-3740019/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((75133/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75133/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (86871101647530396897615052010901/6646776750767225000000000000000000000 : ℝ) := by norm_num
    linear_combination (727935813687/1000000000000 : ℝ)*(base7) + (262507/1000000000000 : ℝ)*(base39) + (7251762561/1000000000000 : ℝ)*(base60) + (566241253893/250000000000 : ℝ)*(major_s2_0) + (566241253893/250000000000 : ℝ)*(major_s2_1) + (566241253893/250000000000 : ℝ)*(major_s2_2) + (4519209/500000000000 : ℝ)*(sp_s2_0) + (8577977/1000000000000 : ℝ)*(sp_s2_1) + (645139364591/250000000000 : ℝ)*(sp_s2_7) + (2580654311623/1000000000000 : ℝ)*(sp_s2_8) + (103226518129/40000000000 : ℝ)*(sp_s2_9) + (1116848180601/500000000000 : ℝ)*(sp_s2_13) + (96456443/1000000000000 : ℝ)*(sp_s2_14) + (509/8000000000 : ℝ)*(sp_s2_22) + (301152109503/200000000000 : ℝ)*(f.failure) + (103226518129/40000000000 : ℝ)*(f.sum) + (2954868155139444559/19196356268750000000000000000000 : ℝ)*base63 + (465061814766397/3567350000000000000000000000 : ℝ)*base65 + (752528140592113/1076225000000000000000000000 : ℝ)*base66 + (16339219438069/22295937500000000000000000 : ℝ)*base69 + (119613384748594146163/308800518050000000000000000000000 : ℝ)*base70 + (1979582638283671/2164075000000000000000000000 : ℝ)*base72 + (1031770182428071/2152450000000000000000000000 : ℝ)*base75 + (618244597628937/1082037500000000000000000000 : ℝ)*base77 + (23011401752171145171/186322529350000000000000000000000 : ℝ)*base78 + (63/1000000000000000 : ℝ)*base87 + (63/1000000000000000 : ℝ)*base89 + (63/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9387/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9387/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (308379763254747065658697267272633/26587107003068900000000000000000000000 : ℝ) := by norm_num
    linear_combination (730879000001/1000000000000 : ℝ)*(base7) + (332251/1000000000000 : ℝ)*(base40) + (11953/40000000000 : ℝ)*(base59) + (2231633465249/1000000000000 : ℝ)*(major_s2_0) + (2231633465249/1000000000000 : ℝ)*(major_s2_1) + (2231633465249/1000000000000 : ℝ)*(major_s2_2) + (27699/8000000000 : ℝ)*(sp_s2_0) + (1950893/1000000000000 : ℝ)*(sp_s2_2) + (8327439/100000000000 : ℝ)*(sp_s2_8) + (2534362703157/1000000000000 : ℝ)*(sp_s2_14) + (1267141445571/500000000000 : ℝ)*(sp_s2_15) + (1267182107319/500000000000 : ℝ)*(sp_s2_16) + (2214455394713/1000000000000 : ℝ)*(sp_s2_20) + (25164421/1000000000000 : ℝ)*(sp_s2_27) + (1483601559133/1000000000000 : ℝ)*(f.failure) + (633591541383/250000000000 : ℝ)*(f.sum) + (98899575479556763511/614283400600000000000000000000000 : ℝ)*base63 + (35107321639831/55739843750000000000000000 : ℝ)*base65 + (359756522064707/2152450000000000000000000000 : ℝ)*base66 + (545223222579113/1426940000000000000000000000 : ℝ)*base69 + (205910188590979048133/617601036100000000000000000000000 : ℝ)*base71 + (315439413153151/4328150000000000000000000000 : ℝ)*base73 + (7638442532406343/8609800000000000000000000000 : ℝ)*base75 + (5629989973532157/8656300000000000000000000000 : ℝ)*base77 + (16555697089785645337/46580632337500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (5707/5000000000000000 : ℝ)*base86 + (5707/5000000000000000 : ℝ)*base88 + (5707/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29253/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29253/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64731205740061416599868524394417/6646776750767225000000000000000000000 : ℝ) := by norm_num
    linear_combination (115008944551/250000000000 : ℝ)*(base7) + (8895013/1000000000000 : ℝ)*(base11) + (895643/500000000000 : ℝ)*(base34) + (105422793927/1000000000000 : ℝ)*(base39) + (12431/20000000000 : ℝ)*(base59) + (2117478068861/1000000000000 : ℝ)*(major_s2_0) + (1058739930073/500000000000 : ℝ)*(major_s2_1) + (1058739930073/500000000000 : ℝ)*(major_s2_2) + (128363257/1000000000000 : ℝ)*(sp_s2_9) + (3975983/200000000000 : ℝ)*(sp_s2_20) + (636738185507/250000000000 : ℝ)*(sp_s2_21) + (2546963428327/1000000000000 : ℝ)*(sp_s2_22) + (254683506507/100000000000 : ℝ)*(sp_s2_23) + (1867725754487/1000000000000 : ℝ)*(sp_s2_27) + (281542329497/200000000000 : ℝ)*(f.failure) + (2546963428327/1000000000000 : ℝ)*(f.sum) + (121210596456943241277/307141700300000000000000000000000 : ℝ)*base63 + (2268127621329921/3567350000000000000000000000 : ℝ)*base65 + (231113548474867/2152450000000000000000000000 : ℝ)*base67 + (758794677165727/713470000000000000000000000 : ℝ)*base69 + (450546113039855100517/617601036100000000000000000000000 : ℝ)*base71 + (646418570697071/1082037500000000000000000000 : ℝ)*base73 + (4146357237794521/4304900000000000000000000000 : ℝ)*base75 + (841562449373283/8656300000000000000000000000 : ℝ)*base77 + (16771287679220837233/46580632337500000000000000000000 : ℝ)*base79 + (63/1000000000000000 : ℝ)*base86 + (937/1000000000000000 : ℝ)*base89 + (937/1000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((86563/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86563/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43049/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43049/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-71347/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-71347/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((75133/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75133/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9387/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9387/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29253/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29253/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303062_s2 p hpa hpb X hX hprev1

#print axioms solution
