-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:56:10.791633+00:00
-- url     : https://prove2.me/submissions/9460ae4a-33c6-4748-95a1-feea453abc41

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
theorem collision_support_c315061_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (946399143/2000000000 : ℝ)*x 0 + (-1524432177/10000000000 : ℝ)*x 1 + (238728931/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946399143/2000000000 : ℝ)^19 ≤ (3876051160591/10000000000000 : ℝ)^15 := by
    have hnat : (946399143 : ℕ)^19*10000000000000^15 ≤ 3876051160591^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946399143 2000000000 3876051160591 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1524432177/10000000000 : ℝ)^19 ≤ (4615728689991/50000000000000 : ℝ)^15 := by
    have hnat : (1524432177 : ℕ)^19*50000000000000^15 ≤ 4615728689991^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524432177 10000000000 4615728689991 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238728931/400000000 : ℝ)^19 ≤ (1040160619923/2000000000000 : ℝ)^15 := by
    have hnat : (238728931 : ℕ)^19*2000000000000^15 ≤ 1040160619923^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238728931 400000000 1040160619923 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(946399143/2000000000 : ℝ), (-1524432177/10000000000 : ℝ), (238728931/400000000 : ℝ)] ![(3876051160591/10000000000000 : ℝ), (4615728689991/50000000000000 : ℝ), (1040160619923/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(946399143/2000000000 : ℝ)|^19 ≤ (3876051160591/10000000000000 : ℝ)^15
        have hw : |(946399143/2000000000 : ℝ)|=(946399143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1524432177/10000000000 : ℝ)|^19 ≤ (4615728689991/50000000000000 : ℝ)^15
        have hw : |(-1524432177/10000000000 : ℝ)|=(1524432177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238728931/400000000 : ℝ)|^19 ≤ (1040160619923/2000000000000 : ℝ)^15
        have hw : |(238728931/400000000 : ℝ)|=(238728931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (30023841/62500000 : ℝ)*x 0 + (1641884181/2500000000 : ℝ)*x 1 + (-416251519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30023841/62500000 : ℝ)^19 ≤ (39507167762419/100000000000000 : ℝ)^15 := by
    have hnat : (30023841 : ℕ)^19*100000000000000^15 ≤ 39507167762419^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30023841 62500000 39507167762419 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1641884181/2500000000 : ℝ)^19 ≤ (14677424483719/25000000000000 : ℝ)^15 := by
    have hnat : (1641884181 : ℕ)^19*25000000000000^15 ≤ 14677424483719^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641884181 2500000000 14677424483719 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416251519/10000000000 : ℝ)^19 ≤ (55722946743/3125000000000 : ℝ)^15 := by
    have hnat : (416251519 : ℕ)^19*3125000000000^15 ≤ 55722946743^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416251519 10000000000 55722946743 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30023841/62500000 : ℝ), (1641884181/2500000000 : ℝ), (-416251519/10000000000 : ℝ)] ![(39507167762419/100000000000000 : ℝ), (14677424483719/25000000000000 : ℝ), (55722946743/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30023841/62500000 : ℝ)|^19 ≤ (39507167762419/100000000000000 : ℝ)^15
        have hw : |(30023841/62500000 : ℝ)|=(30023841/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1641884181/2500000000 : ℝ)|^19 ≤ (14677424483719/25000000000000 : ℝ)^15
        have hw : |(1641884181/2500000000 : ℝ)|=(1641884181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416251519/10000000000 : ℝ)|^19 ≤ (55722946743/3125000000000 : ℝ)^15
        have hw : |(-416251519/10000000000 : ℝ)|=(416251519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1659454363/2500000000 : ℝ)*x 0 + (2582939287/10000000000 : ℝ)*x 1 + (24632497/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1659454363/2500000000 : ℝ)^19 ≤ (29753317055143/50000000000000 : ℝ)^15 := by
    have hnat : (1659454363 : ℕ)^19*50000000000000^15 ≤ 29753317055143^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659454363 2500000000 29753317055143 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2582939287/10000000000 : ℝ)^19 ≤ (1800299043893/10000000000000 : ℝ)^15 := by
    have hnat : (2582939287 : ℕ)^19*10000000000000^15 ≤ 1800299043893^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582939287 10000000000 1800299043893 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24632497/80000000 : ℝ)^19 ≤ (11245187719981/50000000000000 : ℝ)^15 := by
    have hnat : (24632497 : ℕ)^19*50000000000000^15 ≤ 11245187719981^15*80000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24632497 80000000 11245187719981 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1659454363/2500000000 : ℝ), (2582939287/10000000000 : ℝ), (24632497/80000000 : ℝ)] ![(29753317055143/50000000000000 : ℝ), (1800299043893/10000000000000 : ℝ), (11245187719981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1659454363/2500000000 : ℝ)|^19 ≤ (29753317055143/50000000000000 : ℝ)^15
        have hw : |(1659454363/2500000000 : ℝ)|=(1659454363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2582939287/10000000000 : ℝ)|^19 ≤ (1800299043893/10000000000000 : ℝ)^15
        have hw : |(2582939287/10000000000 : ℝ)|=(2582939287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(24632497/80000000 : ℝ)|^19 ≤ (11245187719981/50000000000000 : ℝ)^15
        have hw : |(24632497/80000000 : ℝ)|=(24632497/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-931000531/5000000000 : ℝ)*x 0 + (753786767/2500000000 : ℝ)*x 1 + (3610543133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931000531/5000000000 : ℝ)^19 ≤ (2378690290473/20000000000000 : ℝ)^15 := by
    have hnat : (931000531 : ℕ)^19*20000000000000^15 ≤ 2378690290473^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931000531 5000000000 2378690290473 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (753786767/2500000000 : ℝ)^19 ≤ (10950335818349/50000000000000 : ℝ)^15 := by
    have hnat : (753786767 : ℕ)^19*50000000000000^15 ≤ 10950335818349^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753786767 2500000000 10950335818349 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3610543133/5000000000 : ℝ)^19 ≤ (1034466826489/1562500000000 : ℝ)^15 := by
    have hnat : (3610543133 : ℕ)^19*1562500000000^15 ≤ 1034466826489^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3610543133 5000000000 1034466826489 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-931000531/5000000000 : ℝ), (753786767/2500000000 : ℝ), (3610543133/5000000000 : ℝ)] ![(2378690290473/20000000000000 : ℝ), (10950335818349/50000000000000 : ℝ), (1034466826489/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-931000531/5000000000 : ℝ)|^19 ≤ (2378690290473/20000000000000 : ℝ)^15
        have hw : |(-931000531/5000000000 : ℝ)|=(931000531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(753786767/2500000000 : ℝ)|^19 ≤ (10950335818349/50000000000000 : ℝ)^15
        have hw : |(753786767/2500000000 : ℝ)|=(753786767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3610543133/5000000000 : ℝ)|^19 ≤ (1034466826489/1562500000000 : ℝ)^15
        have hw : |(3610543133/5000000000 : ℝ)|=(3610543133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (890020877/2500000000 : ℝ)*x 0 + (-1157368341/10000000000 : ℝ)*x 1 + (7242747509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890020877/2500000000 : ℝ)^19 ≤ (3378777402801/12500000000000 : ℝ)^15 := by
    have hnat : (890020877 : ℕ)^19*12500000000000^15 ≤ 3378777402801^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890020877 2500000000 3378777402801 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157368341/10000000000 : ℝ)^19 ≤ (407015275291/6250000000000 : ℝ)^15 := by
    have hnat : (1157368341 : ℕ)^19*6250000000000^15 ≤ 407015275291^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157368341 10000000000 407015275291 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7242747509/10000000000 : ℝ)^19 ≤ (33228768178959/50000000000000 : ℝ)^15 := by
    have hnat : (7242747509 : ℕ)^19*50000000000000^15 ≤ 33228768178959^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7242747509 10000000000 33228768178959 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(890020877/2500000000 : ℝ), (-1157368341/10000000000 : ℝ), (7242747509/10000000000 : ℝ)] ![(3378777402801/12500000000000 : ℝ), (407015275291/6250000000000 : ℝ), (33228768178959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(890020877/2500000000 : ℝ)|^19 ≤ (3378777402801/12500000000000 : ℝ)^15
        have hw : |(890020877/2500000000 : ℝ)|=(890020877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1157368341/10000000000 : ℝ)|^19 ≤ (407015275291/6250000000000 : ℝ)^15
        have hw : |(-1157368341/10000000000 : ℝ)|=(1157368341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7242747509/10000000000 : ℝ)|^19 ≤ (33228768178959/50000000000000 : ℝ)^15
        have hw : |(7242747509/10000000000 : ℝ)|=(7242747509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3641588701/10000000000 : ℝ)*x 0 + (7730788887/10000000000 : ℝ)*x 1 + (-3070391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3641588701/10000000000 : ℝ)^19 ≤ (3477057003463/12500000000000 : ℝ)^15 := by
    have hnat : (3641588701 : ℕ)^19*12500000000000^15 ≤ 3477057003463^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3641588701 10000000000 3477057003463 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7730788887/10000000000 : ℝ)^19 ≤ (7217999217911/10000000000000 : ℝ)^15 := by
    have hnat : (7730788887 : ℕ)^19*10000000000000^15 ≤ 7217999217911^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7730788887 10000000000 7217999217911 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3070391/10000000000 : ℝ)^19 ≤ (3551774081/100000000000000 : ℝ)^15 := by
    have hnat : (3070391 : ℕ)^19*100000000000000^15 ≤ 3551774081^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3070391 10000000000 3551774081 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3641588701/10000000000 : ℝ), (7730788887/10000000000 : ℝ), (-3070391/10000000000 : ℝ)] ![(3477057003463/12500000000000 : ℝ), (7217999217911/10000000000000 : ℝ), (3551774081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3641588701/10000000000 : ℝ)|^19 ≤ (3477057003463/12500000000000 : ℝ)^15
        have hw : |(3641588701/10000000000 : ℝ)|=(3641588701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7730788887/10000000000 : ℝ)|^19 ≤ (7217999217911/10000000000000 : ℝ)^15
        have hw : |(7730788887/10000000000 : ℝ)|=(7730788887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3070391/10000000000 : ℝ)|^19 ≤ (3551774081/100000000000000 : ℝ)^15
        have hw : |(-3070391/10000000000 : ℝ)|=(3070391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1210959223/2500000000 : ℝ)*x 0 + (179636103/312500000 : ℝ)*x 1 + (168529309/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1210959223/2500000000 : ℝ)^19 ≤ (3992455155829/10000000000000 : ℝ)^15 := by
    have hnat : (1210959223 : ℕ)^19*10000000000000^15 ≤ 3992455155829^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210959223 2500000000 3992455155829 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179636103/312500000 : ℝ)^19 ≤ (49593173217859/100000000000000 : ℝ)^15 := by
    have hnat : (179636103 : ℕ)^19*100000000000000^15 ≤ 49593173217859^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179636103 312500000 49593173217859 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168529309/1000000000 : ℝ)^19 ≤ (2096455040241/20000000000000 : ℝ)^15 := by
    have hnat : (168529309 : ℕ)^19*20000000000000^15 ≤ 2096455040241^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168529309 1000000000 2096455040241 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1210959223/2500000000 : ℝ), (179636103/312500000 : ℝ), (168529309/1000000000 : ℝ)] ![(3992455155829/10000000000000 : ℝ), (49593173217859/100000000000000 : ℝ), (2096455040241/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1210959223/2500000000 : ℝ)|^19 ≤ (3992455155829/10000000000000 : ℝ)^15
        have hw : |(1210959223/2500000000 : ℝ)|=(1210959223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179636103/312500000 : ℝ)|^19 ≤ (49593173217859/100000000000000 : ℝ)^15
        have hw : |(179636103/312500000 : ℝ)|=(179636103/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168529309/1000000000 : ℝ)|^19 ≤ (2096455040241/20000000000000 : ℝ)^15
        have hw : |(168529309/1000000000 : ℝ)|=(168529309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-737826003/10000000000 : ℝ)*x 0 + (684825821/2000000000 : ℝ)*x 1 + (303836629/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (737826003/10000000000 : ℝ)^19 ≤ (3681925629703/100000000000000 : ℝ)^15 := by
    have hnat : (737826003 : ℕ)^19*100000000000000^15 ≤ 3681925629703^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737826003 10000000000 3681925629703 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684825821/2000000000 : ℝ)^19 ≤ (25729430060097/100000000000000 : ℝ)^15 := by
    have hnat : (684825821 : ℕ)^19*100000000000000^15 ≤ 25729430060097^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684825821 2000000000 25729430060097 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303836629/400000000 : ℝ)^19 ≤ (8823580537543/12500000000000 : ℝ)^15 := by
    have hnat : (303836629 : ℕ)^19*12500000000000^15 ≤ 8823580537543^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303836629 400000000 8823580537543 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-737826003/10000000000 : ℝ), (684825821/2000000000 : ℝ), (303836629/400000000 : ℝ)] ![(3681925629703/100000000000000 : ℝ), (25729430060097/100000000000000 : ℝ), (8823580537543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-737826003/10000000000 : ℝ)|^19 ≤ (3681925629703/100000000000000 : ℝ)^15
        have hw : |(-737826003/10000000000 : ℝ)|=(737826003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684825821/2000000000 : ℝ)|^19 ≤ (25729430060097/100000000000000 : ℝ)^15
        have hw : |(684825821/2000000000 : ℝ)|=(684825821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(303836629/400000000 : ℝ)|^19 ≤ (8823580537543/12500000000000 : ℝ)^15
        have hw : |(303836629/400000000 : ℝ)|=(303836629/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2732418183/10000000000 : ℝ)*x 0 + (-399818211/2500000000 : ℝ)*x 1 + (7618792517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2732418183/10000000000 : ℝ)^19 ≤ (2416590650029/12500000000000 : ℝ)^15 := by
    have hnat : (2732418183 : ℕ)^19*12500000000000^15 ≤ 2416590650029^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732418183 10000000000 2416590650029 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399818211/2500000000 : ℝ)^19 ≤ (1961847484583/20000000000000 : ℝ)^15 := by
    have hnat : (399818211 : ℕ)^19*20000000000000^15 ≤ 1961847484583^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399818211 2500000000 1961847484583 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7618792517/10000000000 : ℝ)^19 ≤ (17714509339903/25000000000000 : ℝ)^15 := by
    have hnat : (7618792517 : ℕ)^19*25000000000000^15 ≤ 17714509339903^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7618792517 10000000000 17714509339903 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2732418183/10000000000 : ℝ), (-399818211/2500000000 : ℝ), (7618792517/10000000000 : ℝ)] ![(2416590650029/12500000000000 : ℝ), (1961847484583/20000000000000 : ℝ), (17714509339903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2732418183/10000000000 : ℝ)|^19 ≤ (2416590650029/12500000000000 : ℝ)^15
        have hw : |(2732418183/10000000000 : ℝ)|=(2732418183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399818211/2500000000 : ℝ)|^19 ≤ (1961847484583/20000000000000 : ℝ)^15
        have hw : |(-399818211/2500000000 : ℝ)|=(399818211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7618792517/10000000000 : ℝ)|^19 ≤ (17714509339903/25000000000000 : ℝ)^15
        have hw : |(7618792517/10000000000 : ℝ)|=(7618792517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (859645163/1250000000 : ℝ)*x 0 + (2313973099/5000000000 : ℝ)*x 1 + (-1413711/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859645163/1250000000 : ℝ)^19 ≤ (62237432329429/100000000000000 : ℝ)^15 := by
    have hnat : (859645163 : ℕ)^19*100000000000000^15 ≤ 62237432329429^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859645163 1250000000 62237432329429 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2313973099/5000000000 : ℝ)^19 ≤ (18842065947107/50000000000000 : ℝ)^15 := by
    have hnat : (2313973099 : ℕ)^19*50000000000000^15 ≤ 18842065947107^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313973099 5000000000 18842065947107 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1413711/400000000 : ℝ)^19 ≤ (3137430707/4000000000000 : ℝ)^15 := by
    have hnat : (1413711 : ℕ)^19*4000000000000^15 ≤ 3137430707^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413711 400000000 3137430707 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859645163/1250000000 : ℝ), (2313973099/5000000000 : ℝ), (-1413711/400000000 : ℝ)] ![(62237432329429/100000000000000 : ℝ), (18842065947107/50000000000000 : ℝ), (3137430707/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859645163/1250000000 : ℝ)|^19 ≤ (62237432329429/100000000000000 : ℝ)^15
        have hw : |(859645163/1250000000 : ℝ)|=(859645163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2313973099/5000000000 : ℝ)|^19 ≤ (18842065947107/50000000000000 : ℝ)^15
        have hw : |(2313973099/5000000000 : ℝ)|=(2313973099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1413711/400000000 : ℝ)|^19 ≤ (3137430707/4000000000000 : ℝ)^15
        have hw : |(-1413711/400000000 : ℝ)|=(1413711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (79359803/100000000 : ℝ)*x 0 + (476149879/2000000000 : ℝ)*x 1 + (189190249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79359803/100000000 : ℝ)^19 ≤ (37307608184383/50000000000000 : ℝ)^15 := by
    have hnat : (79359803 : ℕ)^19*50000000000000^15 ≤ 37307608184383^15*100000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79359803 100000000 37307608184383 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476149879/2000000000 : ℝ)^19 ≤ (4059233244343/25000000000000 : ℝ)^15 := by
    have hnat : (476149879 : ℕ)^19*25000000000000^15 ≤ 4059233244343^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476149879 2000000000 4059233244343 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189190249/1250000000 : ℝ)^19 ≤ (9147850644411/100000000000000 : ℝ)^15 := by
    have hnat : (189190249 : ℕ)^19*100000000000000^15 ≤ 9147850644411^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189190249 1250000000 9147850644411 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(79359803/100000000 : ℝ), (476149879/2000000000 : ℝ), (189190249/1250000000 : ℝ)] ![(37307608184383/50000000000000 : ℝ), (4059233244343/25000000000000 : ℝ), (9147850644411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(79359803/100000000 : ℝ)|^19 ≤ (37307608184383/50000000000000 : ℝ)^15
        have hw : |(79359803/100000000 : ℝ)|=(79359803/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(476149879/2000000000 : ℝ)|^19 ≤ (4059233244343/25000000000000 : ℝ)^15
        have hw : |(476149879/2000000000 : ℝ)|=(476149879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(189190249/1250000000 : ℝ)|^19 ≤ (9147850644411/100000000000000 : ℝ)^15
        have hw : |(189190249/1250000000 : ℝ)|=(189190249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-473385011/10000000000 : ℝ)*x 0 + (6115316487/10000000000 : ℝ)*x 1 + (1313740411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473385011/10000000000 : ℝ)^19 ≤ (524660511809/25000000000000 : ℝ)^15 := by
    have hnat : (473385011 : ℕ)^19*25000000000000^15 ≤ 524660511809^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473385011 10000000000 524660511809 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6115316487/10000000000 : ℝ)^19 ≤ (53636939374649/100000000000000 : ℝ)^15 := by
    have hnat : (6115316487 : ℕ)^19*100000000000000^15 ≤ 53636939374649^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6115316487 10000000000 53636939374649 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313740411/2500000000 : ℝ)^19 ≤ (11066104641053/25000000000000 : ℝ)^15 := by
    have hnat : (1313740411 : ℕ)^19*25000000000000^15 ≤ 11066104641053^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313740411 2500000000 11066104641053 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473385011/10000000000 : ℝ), (6115316487/10000000000 : ℝ), (1313740411/2500000000 : ℝ)] ![(524660511809/25000000000000 : ℝ), (53636939374649/100000000000000 : ℝ), (11066104641053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473385011/10000000000 : ℝ)|^19 ≤ (524660511809/25000000000000 : ℝ)^15
        have hw : |(-473385011/10000000000 : ℝ)|=(473385011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6115316487/10000000000 : ℝ)|^19 ≤ (53636939374649/100000000000000 : ℝ)^15
        have hw : |(6115316487/10000000000 : ℝ)|=(6115316487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313740411/2500000000 : ℝ)|^19 ≤ (11066104641053/25000000000000 : ℝ)^15
        have hw : |(1313740411/2500000000 : ℝ)|=(1313740411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3353024773/5000000000 : ℝ)*x 0 + (-81657731/2000000000 : ℝ)*x 1 + (29102269/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3353024773/5000000000 : ℝ)^19 ≤ (12056499214533/20000000000000 : ℝ)^15 := by
    have hnat : (3353024773 : ℕ)^19*20000000000000^15 ≤ 12056499214533^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3353024773 5000000000 12056499214533 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81657731/2000000000 : ℝ)^19 ≤ (108752340701/6250000000000 : ℝ)^15 := by
    have hnat : (81657731 : ℕ)^19*6250000000000^15 ≤ 108752340701^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81657731 2000000000 108752340701 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29102269/62500000 : ℝ)^19 ≤ (18988733232311/50000000000000 : ℝ)^15 := by
    have hnat : (29102269 : ℕ)^19*50000000000000^15 ≤ 18988733232311^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29102269 62500000 18988733232311 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3353024773/5000000000 : ℝ), (-81657731/2000000000 : ℝ), (29102269/62500000 : ℝ)] ![(12056499214533/20000000000000 : ℝ), (108752340701/6250000000000 : ℝ), (18988733232311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3353024773/5000000000 : ℝ)|^19 ≤ (12056499214533/20000000000000 : ℝ)^15
        have hw : |(3353024773/5000000000 : ℝ)|=(3353024773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81657731/2000000000 : ℝ)|^19 ≤ (108752340701/6250000000000 : ℝ)^15
        have hw : |(-81657731/2000000000 : ℝ)|=(81657731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29102269/62500000 : ℝ)|^19 ≤ (18988733232311/50000000000000 : ℝ)^15
        have hw : |(29102269/62500000 : ℝ)|=(29102269/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (586191967/2000000000 : ℝ)*x 0 + (506792749/625000000 : ℝ)*x 1 + (-245058793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (586191967/2000000000 : ℝ)^19 ≤ (10564505395473/50000000000000 : ℝ)^15 := by
    have hnat : (586191967 : ℕ)^19*50000000000000^15 ≤ 10564505395473^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586191967 2000000000 10564505395473 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506792749/625000000 : ℝ)^19 ≤ (19169486697857/25000000000000 : ℝ)^15 := by
    have hnat : (506792749 : ℕ)^19*25000000000000^15 ≤ 19169486697857^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506792749 625000000 19169486697857 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245058793/5000000000 : ℝ)^19 ≤ (219304240161/10000000000000 : ℝ)^15 := by
    have hnat : (245058793 : ℕ)^19*10000000000000^15 ≤ 219304240161^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245058793 5000000000 219304240161 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(586191967/2000000000 : ℝ), (506792749/625000000 : ℝ), (-245058793/5000000000 : ℝ)] ![(10564505395473/50000000000000 : ℝ), (19169486697857/25000000000000 : ℝ), (219304240161/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(586191967/2000000000 : ℝ)|^19 ≤ (10564505395473/50000000000000 : ℝ)^15
        have hw : |(586191967/2000000000 : ℝ)|=(586191967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506792749/625000000 : ℝ)|^19 ≤ (19169486697857/25000000000000 : ℝ)^15
        have hw : |(506792749/625000000 : ℝ)|=(506792749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245058793/5000000000 : ℝ)|^19 ≤ (219304240161/10000000000000 : ℝ)^15
        have hw : |(-245058793/5000000000 : ℝ)|=(245058793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315061_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8537376269/10000000000 : ℝ)*x 0 + (1560842707/10000000000 : ℝ)*x 1 + (1446767969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8537376269/10000000000 : ℝ)^19 ≤ (81848539680097/100000000000000 : ℝ)^15 := by
    have hnat : (8537376269 : ℕ)^19*100000000000000^15 ≤ 81848539680097^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8537376269 10000000000 81848539680097 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560842707/10000000000 : ℝ)^19 ≤ (2377907292141/25000000000000 : ℝ)^15 := by
    have hnat : (1560842707 : ℕ)^19*25000000000000^15 ≤ 2377907292141^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560842707 10000000000 2377907292141 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1446767969/10000000000 : ℝ)^19 ≤ (13823729819/160000000000 : ℝ)^15 := by
    have hnat : (1446767969 : ℕ)^19*160000000000^15 ≤ 13823729819^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446767969 10000000000 13823729819 160000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8537376269/10000000000 : ℝ), (1560842707/10000000000 : ℝ), (1446767969/10000000000 : ℝ)] ![(81848539680097/100000000000000 : ℝ), (2377907292141/25000000000000 : ℝ), (13823729819/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8537376269/10000000000 : ℝ)|^19 ≤ (81848539680097/100000000000000 : ℝ)^15
        have hw : |(8537376269/10000000000 : ℝ)|=(8537376269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560842707/10000000000 : ℝ)|^19 ≤ (2377907292141/25000000000000 : ℝ)^15
        have hw : |(1560842707/10000000000 : ℝ)|=(1560842707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1446767969/10000000000 : ℝ)|^19 ≤ (13823729819/160000000000 : ℝ)^15
        have hw : |(1446767969/10000000000 : ℝ)|=(1446767969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315061_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((20281/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20281/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39881/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39881/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76449/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76449/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11681/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11681/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30409/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55803/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55803/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (20281/25000 : ℝ) ^ (75/16 : ℝ) ≤ (1500367331311232819/4000000000000000000 : ℝ) := by
    have hpowers : (20281/25000 : ℝ)^75 ≤ (1500367331311232819/4000000000000000000 : ℝ)^16 := by
      have hnat : (20281 : ℕ)^75*4000000000000000000^16 ≤ 1500367331311232819^16*25000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20281 25000 1500367331311232819 4000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20281/25000 : ℝ)) (X := (1500367331311232819/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (5500367331311232819/4000000000000000000 : ℝ) ≤ (2140625816841353/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (5500367331311232819/4000000000000000000 : ℝ)^16 ≤ (2140625816841353/2000000000000000 : ℝ)^75 := by
      have hnat : (5500367331311232819 : ℕ)^16*2000000000000000^75 ≤ 2140625816841353^75*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5500367331311232819 4000000000000000000 2140625816841353 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2140625816841353/2000000000000000 : ℝ)) (X := (5500367331311232819/4000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3500367331311232819/2000000000000000000 : ℝ) ≤ (1408535681911083/1250000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3500367331311232819/2000000000000000000 : ℝ)^16 ≤ (1408535681911083/1250000000000000 : ℝ)^75 := by
      have hnat : (3500367331311232819 : ℕ)^16*1250000000000000^75 ≤ 1408535681911083^75*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3500367331311232819 2000000000000000000 1408535681911083 1250000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1408535681911083/1250000000000000 : ℝ)) (X := (3500367331311232819/2000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(140625816841353/1622480000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(565156371081899/8112400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (20281/25000 : ℝ)) (alpha := (140625816841353/1622480000000000 : ℝ)) (beta := (565156371081899/8112400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20281/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(140625816841353/1622480000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(565156371081899/8112400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (39881/50000 : ℝ) ^ (75/16 : ℝ) ≤ (8661815396595673403/25000000000000000000 : ℝ) := by
    have hpowers : (39881/50000 : ℝ)^75 ≤ (8661815396595673403/25000000000000000000 : ℝ)^16 := by
      have hnat : (39881 : ℕ)^75*25000000000000000000^16 ≤ 8661815396595673403^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39881 50000 8661815396595673403 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39881/50000 : ℝ)) (X := (8661815396595673403/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (33661815396595673403/25000000000000000000 : ℝ) ≤ (10655213072426853/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (33661815396595673403/25000000000000000000 : ℝ)^16 ≤ (10655213072426853/10000000000000000 : ℝ)^75 := by
      have hnat : (33661815396595673403 : ℕ)^16*10000000000000000^75 ≤ 10655213072426853^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33661815396595673403 25000000000000000000 10655213072426853 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10655213072426853/10000000000000000 : ℝ)) (X := (33661815396595673403/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (21161815396595673403/12500000000000000000 : ℝ) ≤ (349644881961743/312500000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (21161815396595673403/12500000000000000000 : ℝ)^16 ≤ (349644881961743/312500000000000 : ℝ)^75 := by
      have hnat : (21161815396595673403 : ℕ)^16*312500000000000^75 ≤ 349644881961743^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21161815396595673403 12500000000000000000 349644881961743 312500000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (349644881961743/312500000000000 : ℝ)) (X := (21161815396595673403/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(655213072426853/7976200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(533423150348923/7976200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (39881/50000 : ℝ)) (alpha := (655213072426853/7976200000000000 : ℝ)) (beta := (533423150348923/7976200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39881/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(655213072426853/7976200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(533423150348923/7976200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (76449/100000 : ℝ) ^ (75/16 : ℝ) ≤ (28399150839182189517/100000000000000000000 : ℝ) := by
    have hpowers : (76449/100000 : ℝ)^75 ≤ (28399150839182189517/100000000000000000000 : ℝ)^16 := by
      have hnat : (76449 : ℕ)^75*100000000000000000000^16 ≤ 28399150839182189517^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76449 100000 28399150839182189517 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76449/100000 : ℝ)) (X := (28399150839182189517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (128399150839182189517/100000000000000000000 : ℝ) ≤ (10547752379075077/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (128399150839182189517/100000000000000000000 : ℝ)^16 ≤ (10547752379075077/10000000000000000 : ℝ)^75 := by
      have hnat : (128399150839182189517 : ℕ)^16*10000000000000000^75 ≤ 10547752379075077^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128399150839182189517 100000000000000000000 10547752379075077 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10547752379075077/10000000000000000 : ℝ)) (X := (128399150839182189517/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (78399150839182189517/50000000000000000000 : ℝ) ≤ (5503548861995711/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (78399150839182189517/50000000000000000000 : ℝ)^16 ≤ (5503548861995711/5000000000000000 : ℝ)^75 := by
      have hnat : (78399150839182189517 : ℕ)^16*5000000000000000^75 ≤ 5503548861995711^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78399150839182189517 50000000000000000000 5503548861995711 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5503548861995711/5000000000000000 : ℝ)) (X := (78399150839182189517/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(182584126358359/2548300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(30623022994423/509660000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (76449/100000 : ℝ)) (alpha := (182584126358359/2548300000000000 : ℝ)) (beta := (30623022994423/509660000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (76449/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(182584126358359/2548300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(30623022994423/509660000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((946399143/2000000000 : ℝ)*X 1 0+(-1524432177/10000000000 : ℝ)*X 1 1+(238728931/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((30023841/62500000 : ℝ)*X 2 0+(1641884181/2500000000 : ℝ)*X 2 1+(-416251519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1659454363/2500000000 : ℝ)*X 0 0+(2582939287/10000000000 : ℝ)*X 0 1+(24632497/80000000 : ℝ)*X 0 2+(1659454363/2500000000 : ℝ)*X 1 0+(2582939287/10000000000 : ℝ)*X 1 1+(24632497/80000000 : ℝ)*X 1 2+(1659454363/2500000000 : ℝ)*X 2 0+(2582939287/10000000000 : ℝ)*X 2 1+(24632497/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-931000531/5000000000 : ℝ)*X 0 0+(753786767/2500000000 : ℝ)*X 0 1+(3610543133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((890020877/2500000000 : ℝ)*X 1 0+(-1157368341/10000000000 : ℝ)*X 1 1+(7242747509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3641588701/10000000000 : ℝ)*X 2 0+(7730788887/10000000000 : ℝ)*X 2 1+(-3070391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1210959223/2500000000 : ℝ)*X 0 0+(179636103/312500000 : ℝ)*X 0 1+(168529309/1000000000 : ℝ)*X 0 2+(1210959223/2500000000 : ℝ)*X 1 0+(179636103/312500000 : ℝ)*X 1 1+(168529309/1000000000 : ℝ)*X 1 2+(1210959223/2500000000 : ℝ)*X 2 0+(179636103/312500000 : ℝ)*X 2 1+(168529309/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-737826003/10000000000 : ℝ)*X 0 0+(684825821/2000000000 : ℝ)*X 0 1+(303836629/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2732418183/10000000000 : ℝ)*X 1 0+(-399818211/2500000000 : ℝ)*X 1 1+(7618792517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((859645163/1250000000 : ℝ)*X 2 0+(2313973099/5000000000 : ℝ)*X 2 1+(-1413711/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((79359803/100000000 : ℝ)*X 0 0+(476149879/2000000000 : ℝ)*X 0 1+(189190249/1250000000 : ℝ)*X 0 2+(79359803/100000000 : ℝ)*X 1 0+(476149879/2000000000 : ℝ)*X 1 1+(189190249/1250000000 : ℝ)*X 1 2+(79359803/100000000 : ℝ)*X 2 0+(476149879/2000000000 : ℝ)*X 2 1+(189190249/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-473385011/10000000000 : ℝ)*X 0 0+(6115316487/10000000000 : ℝ)*X 0 1+(1313740411/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3353024773/5000000000 : ℝ)*X 1 0+(-81657731/2000000000 : ℝ)*X 1 1+(29102269/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((586191967/2000000000 : ℝ)*X 2 0+(506792749/625000000 : ℝ)*X 2 1+(-245058793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8537376269/10000000000 : ℝ)*X 0 0+(1560842707/10000000000 : ℝ)*X 0 1+(1446767969/10000000000 : ℝ)*X 0 2+(8537376269/10000000000 : ℝ)*X 1 0+(1560842707/10000000000 : ℝ)*X 1 1+(1446767969/10000000000 : ℝ)*X 1 2+(8537376269/10000000000 : ℝ)*X 2 0+(1560842707/10000000000 : ℝ)*X 2 1+(1446767969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((11681/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11681/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4554706633014759614853129/635179701875000000000000000000 : ℝ) := by norm_num
    linear_combination (39895579319/62500000000 : ℝ)*(base7) + (121703/50000000000 : ℝ)*(base13) + (56157/500000000000 : ℝ)*(base50) + (22485014001/100000000000 : ℝ)*(base59) + (53193519621/20000000000 : ℝ)*(major_s1_0) + (53193519621/20000000000 : ℝ)*(major_s1_1) + (53193519621/20000000000 : ℝ)*(major_s1_2) + (253461/40000000000 : ℝ)*(sp_s1_1) + (3425127919469/1000000000000 : ℝ)*(sp_s1_7) + (171256433579/50000000000 : ℝ)*(sp_s1_8) + (3425155590619/1000000000000 : ℝ)*(sp_s1_9) + (1080555682551/500000000000 : ℝ)*(sp_s1_13) + (25237091/1000000000000 : ℝ)*(sp_s1_14) + (4116503/200000000000 : ℝ)*(sp_s1_15) + (761391047999/500000000000 : ℝ)*(f.failure) + (3425155590619/1000000000000 : ℝ)*(f.sum) + (6950714968322828633/20325750460000000000000000000000 : ℝ)*base62 + (7124053541607/15926875000000000000000000 : ℝ)*base64 + (147430649418743/797620000000000000000000000 : ℝ)*base66 + (84764191106157/254830000000000000000000000 : ℝ)*base68 + (192038238468175177/1216048760000000000000000000000 : ℝ)*base70 + (15309632764333/32449600000000000000000000 : ℝ)*base72 + (253229334867521/797620000000000000000000000 : ℝ)*base74 + (33134445572189/162248000000000000000000000 : ℝ)*base77 + (13725705894867433381/32353062440000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (42659/50000000000000000 : ℝ)*base86 + (42659/50000000000000000 : ℝ)*base88 + (42659/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30409/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (165433374496293421025711425827/12124310149390000000000000000000000 : ℝ) := by norm_num
    linear_combination (723681333271/1000000000000 : ℝ)*(base7) + (14821137/1000000000000 : ℝ)*(base19) + (5957/31250000000 : ℝ)*(base53) + (505263681919/250000000000 : ℝ)*(major_s1_0) + (505263681919/250000000000 : ℝ)*(major_s1_1) + (505263634263/250000000000 : ℝ)*(major_s1_2) + (1022397/100000000000 : ℝ)*(sp_s1_6) + (214553/500000000000 : ℝ)*(sp_s1_7) + (96523441/1000000000000 : ℝ)*(sp_s1_8) + (2463887111621/1000000000000 : ℝ)*(sp_s1_14) + (615944049037/250000000000 : ℝ)*(sp_s1_15) + (49277754627/20000000000 : ℝ)*(sp_s1_16) + (940376559131/500000000000 : ℝ)*(sp_s1_20) + (7647877/125000000000 : ℝ)*(sp_s1_27) + (578571595989/500000000000 : ℝ)*(f.failure) + (49277754627/20000000000 : ℝ)*(f.sum) + (78025702358761849/254071880750000000000000000000 : ℝ)*base63 + (125363655592713/254830000000000000000000000 : ℝ)*base64 + (770837477082379/997025000000000000000000000 : ℝ)*base66 + (27505465203797/637075000000000000000000000 : ℝ)*base69 + (25653068889589897/608024380000000000000000000000 : ℝ)*base70 + (141705369232649/2028100000000000000000000000 : ℝ)*base72 + (346189127363587/1994050000000000000000000000 : ℝ)*base75 + (70473079944097/405620000000000000000000000 : ℝ)*base76 + (53751141871429089/3235306244000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (42751/50000000000000000 : ℝ)*base87 + (42751/50000000000000000 : ℝ)*base89 + (42751/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55803/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55803/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1443606453568797634395982251/101628752300000000000000000000000 : ℝ) := by norm_num
    linear_combination (519319817191/1000000000000 : ℝ)*(base7) + (225861/40000000000 : ℝ)*(base11) + (2513181919/15625000000 : ℝ)*(base40) + (14583228331/250000000000 : ℝ)*(base59) + (2027915369533/1000000000000 : ℝ)*(major_s1_0) + (2027915369533/1000000000000 : ℝ)*(major_s1_1) + (2027915369533/1000000000000 : ℝ)*(major_s1_2) + (482341/62500000000 : ℝ)*(sp_s1_1) + (610067/1000000000000 : ℝ)*(sp_s1_2) + (70964633/500000000000 : ℝ)*(sp_s1_9) + (2592582909221/1000000000000 : ℝ)*(sp_s1_21) + (259258083829/100000000000 : ℝ)*(sp_s1_22) + (1296223008207/500000000000 : ℝ)*(sp_s1_23) + (1680391029973/1000000000000 : ℝ)*(sp_s1_27) + (580535606391/500000000000 : ℝ)*(f.failure) + (1296294277873/500000000000 : ℝ)*(f.sum) + (62282893667715825879/203257504600000000000000000000000 : ℝ)*base62 + (272646653287833/509660000000000000000000000 : ℝ)*base65 + (2779023429666139/7976200000000000000000000000 : ℝ)*base67 + (150870268421237/2548300000000000000000000000 : ℝ)*base69 + (97453975695619751/486419504000000000000000000000 : ℝ)*base71 + (2036047079615287/8112400000000000000000000000 : ℝ)*base73 + (2085476316567411/7976200000000000000000000000 : ℝ)*base74 + (249396066454627/1622480000000000000000000000 : ℝ)*base76 + (2282254423066665667/12941224976000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (4331/50000000000000000 : ℝ)*base86 + (4331/50000000000000000 : ℝ)*base88 + (4331/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((20281/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20281/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39881/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39881/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76449/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76449/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11681/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11681/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30409/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30409/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55803/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55803/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315061_s1 p hpa hpb X hX hprev0

#print axioms solution
