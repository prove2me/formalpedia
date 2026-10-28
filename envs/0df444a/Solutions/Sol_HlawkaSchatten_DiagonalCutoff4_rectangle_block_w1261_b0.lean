-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1261_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:54:19.65244+00:00
-- url     : https://prove2.me/submissions/61201924-4f19-478d-89ba-4e17f2b8c261

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
theorem support_rectangle_w1261_s0_0 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-927355807/5000000000 : ℝ)*x 0 + (3013616631/5000000000 : ℝ)*x 1 + (599416947/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927355807/5000000000 : ℝ)^4227 ≤ (10822912522687/100000000000000 : ℝ)^3203 := by
    have hnat : (927355807 : ℕ)^4227*100000000000000^3203 ≤ 10822912522687^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927355807 5000000000 10822912522687 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3013616631/5000000000 : ℝ)^4227 ≤ (12816270673319/25000000000000 : ℝ)^3203 := by
    have hnat : (3013616631 : ℕ)^4227*25000000000000^3203 ≤ 12816270673319^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013616631 5000000000 12816270673319 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599416947/1250000000 : ℝ)^4227 ≤ (37912004772433/100000000000000 : ℝ)^3203 := by
    have hnat : (599416947 : ℕ)^4227*100000000000000^3203 ≤ 37912004772433^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599416947 1250000000 37912004772433 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-927355807/5000000000 : ℝ), (3013616631/5000000000 : ℝ), (599416947/1250000000 : ℝ)] ![(10822912522687/100000000000000 : ℝ), (12816270673319/25000000000000 : ℝ), (37912004772433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-927355807/5000000000 : ℝ)|^4227 ≤ (10822912522687/100000000000000 : ℝ)^3203
        have hw : |(-927355807/5000000000 : ℝ)|=(927355807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3013616631/5000000000 : ℝ)|^4227 ≤ (12816270673319/25000000000000 : ℝ)^3203
        have hw : |(3013616631/5000000000 : ℝ)|=(3013616631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599416947/1250000000 : ℝ)|^4227 ≤ (37912004772433/100000000000000 : ℝ)^3203
        have hw : |(599416947/1250000000 : ℝ)|=(599416947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s0_1 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5510089049/10000000000 : ℝ)*x 0 + (-1279225151/5000000000 : ℝ)*x 1 + (2397667773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510089049/10000000000 : ℝ)^4227 ≤ (45541460573271/100000000000000 : ℝ)^3203 := by
    have hnat : (5510089049 : ℕ)^4227*100000000000000^3203 ≤ 45541460573271^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510089049 10000000000 45541460573271 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279225151/5000000000 : ℝ)^4227 ≤ (8273267475919/50000000000000 : ℝ)^3203 := by
    have hnat : (1279225151 : ℕ)^4227*50000000000000^3203 ≤ 8273267475919^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279225151 5000000000 8273267475919 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397667773/5000000000 : ℝ)^4227 ≤ (18956002229713/50000000000000 : ℝ)^3203 := by
    have hnat : (2397667773 : ℕ)^4227*50000000000000^3203 ≤ 18956002229713^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397667773 5000000000 18956002229713 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510089049/10000000000 : ℝ), (-1279225151/5000000000 : ℝ), (2397667773/5000000000 : ℝ)] ![(45541460573271/100000000000000 : ℝ), (8273267475919/50000000000000 : ℝ), (18956002229713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510089049/10000000000 : ℝ)|^4227 ≤ (45541460573271/100000000000000 : ℝ)^3203
        have hw : |(5510089049/10000000000 : ℝ)|=(5510089049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1279225151/5000000000 : ℝ)|^4227 ≤ (8273267475919/50000000000000 : ℝ)^3203
        have hw : |(-1279225151/5000000000 : ℝ)|=(1279225151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397667773/5000000000 : ℝ)|^4227 ≤ (18956002229713/50000000000000 : ℝ)^3203
        have hw : |(2397667773/5000000000 : ℝ)|=(2397667773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s0_2 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2755044541/5000000000 : ℝ)*x 0 + (2397667773/5000000000 : ℝ)*x 1 + (-2558450259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755044541/5000000000 : ℝ)^4227 ≤ (45541460933217/100000000000000 : ℝ)^3203 := by
    have hnat : (2755044541 : ℕ)^4227*100000000000000^3203 ≤ 45541460933217^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755044541 5000000000 45541460933217 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397667773/5000000000 : ℝ)^4227 ≤ (18956002229713/50000000000000 : ℝ)^3203 := by
    have hnat : (2397667773 : ℕ)^4227*50000000000000^3203 ≤ 18956002229713^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397667773 5000000000 18956002229713 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2558450259/10000000000 : ℝ)^4227 ≤ (32317450361/195312500000 : ℝ)^3203 := by
    have hnat : (2558450259 : ℕ)^4227*195312500000^3203 ≤ 32317450361^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558450259 10000000000 32317450361 195312500000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755044541/5000000000 : ℝ), (2397667773/5000000000 : ℝ), (-2558450259/10000000000 : ℝ)] ![(45541460933217/100000000000000 : ℝ), (18956002229713/50000000000000 : ℝ), (32317450361/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755044541/5000000000 : ℝ)|^4227 ≤ (45541460933217/100000000000000 : ℝ)^3203
        have hw : |(2755044541/5000000000 : ℝ)|=(2755044541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2397667773/5000000000 : ℝ)|^4227 ≤ (18956002229713/50000000000000 : ℝ)^3203
        have hw : |(2397667773/5000000000 : ℝ)|=(2397667773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2558450259/10000000000 : ℝ)|^4227 ≤ (32317450361/195312500000 : ℝ)^3203
        have hw : |(-2558450259/10000000000 : ℝ)|=(2558450259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s0_3 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209576667/500000000 : ℝ)*x 0 + (3116193403/10000000000 : ℝ)*x 1 + (1406088951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209576667/500000000 : ℝ)^4227 ≤ (31742815360533/100000000000000 : ℝ)^3203 := by
    have hnat : (209576667 : ℕ)^4227*100000000000000^3203 ≤ 31742815360533^3203*500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209576667 500000000 31742815360533 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116193403/10000000000 : ℝ)^4227 ≤ (21465251606027/100000000000000 : ℝ)^3203 := by
    have hnat : (3116193403 : ℕ)^4227*100000000000000^3203 ≤ 21465251606027^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116193403 10000000000 21465251606027 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1406088951/2500000000 : ℝ)^4227 ≤ (46791933016853/100000000000000 : ℝ)^3203 := by
    have hnat : (1406088951 : ℕ)^4227*100000000000000^3203 ≤ 46791933016853^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406088951 2500000000 46791933016853 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209576667/500000000 : ℝ), (3116193403/10000000000 : ℝ), (1406088951/2500000000 : ℝ)] ![(31742815360533/100000000000000 : ℝ), (21465251606027/100000000000000 : ℝ), (46791933016853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209576667/500000000 : ℝ)|^4227 ≤ (31742815360533/100000000000000 : ℝ)^3203
        have hw : |(209576667/500000000 : ℝ)|=(209576667/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116193403/10000000000 : ℝ)|^4227 ≤ (21465251606027/100000000000000 : ℝ)^3203
        have hw : |(3116193403/10000000000 : ℝ)|=(3116193403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1406088951/2500000000 : ℝ)|^4227 ≤ (46791933016853/100000000000000 : ℝ)^3203
        have hw : |(1406088951/2500000000 : ℝ)|=(1406088951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s0_4 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929757647/5000000000 : ℝ)*x 0 + (1206761737/2500000000 : ℝ)*x 1 + (1198880099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929757647/5000000000 : ℝ)^4227 ≤ (217198412463/2000000000000 : ℝ)^3203 := by
    have hnat : (929757647 : ℕ)^4227*2000000000000^3203 ≤ 217198412463^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929757647 5000000000 217198412463 2000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206761737/2500000000 : ℝ)^4227 ≤ (38243216910707/100000000000000 : ℝ)^3203 := by
    have hnat : (1206761737 : ℕ)^4227*100000000000000^3203 ≤ 38243216910707^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206761737 2500000000 38243216910707 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198880099/2000000000 : ℝ)^4227 ≤ (25448431228061/50000000000000 : ℝ)^3203 := by
    have hnat : (1198880099 : ℕ)^4227*50000000000000^3203 ≤ 25448431228061^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198880099 2000000000 25448431228061 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929757647/5000000000 : ℝ), (1206761737/2500000000 : ℝ), (1198880099/2000000000 : ℝ)] ![(217198412463/2000000000000 : ℝ), (38243216910707/100000000000000 : ℝ), (25448431228061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929757647/5000000000 : ℝ)|^4227 ≤ (217198412463/2000000000000 : ℝ)^3203
        have hw : |(-929757647/5000000000 : ℝ)|=(929757647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206761737/2500000000 : ℝ)|^4227 ≤ (38243216910707/100000000000000 : ℝ)^3203
        have hw : |(1206761737/2500000000 : ℝ)|=(1206761737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198880099/2000000000 : ℝ)|^4227 ≤ (25448431228061/50000000000000 : ℝ)^3203
        have hw : |(1198880099/2000000000 : ℝ)|=(1198880099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s0_5 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (646853541/1250000000 : ℝ)*x 0 + (-271876589/2000000000 : ℝ)*x 1 + (599440291/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646853541/1250000000 : ℝ)^4227 ≤ (1310021497207/3125000000000 : ℝ)^3203 := by
    have hnat : (646853541 : ℕ)^4227*3125000000000^3203 ≤ 1310021497207^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646853541 1250000000 1310021497207 3125000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271876589/2000000000 : ℝ)^4227 ≤ (7182422561147/100000000000000 : ℝ)^3203 := by
    have hnat : (271876589 : ℕ)^4227*100000000000000^3203 ≤ 7182422561147^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271876589 2000000000 7182422561147 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599440291/1000000000 : ℝ)^4227 ≤ (50896889516741/100000000000000 : ℝ)^3203 := by
    have hnat : (599440291 : ℕ)^4227*100000000000000^3203 ≤ 50896889516741^3203*1000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599440291 1000000000 50896889516741 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646853541/1250000000 : ℝ), (-271876589/2000000000 : ℝ), (599440291/1000000000 : ℝ)] ![(1310021497207/3125000000000 : ℝ), (7182422561147/100000000000000 : ℝ), (50896889516741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646853541/1250000000 : ℝ)|^4227 ≤ (1310021497207/3125000000000 : ℝ)^3203
        have hw : |(646853541/1250000000 : ℝ)|=(646853541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-271876589/2000000000 : ℝ)|^4227 ≤ (7182422561147/100000000000000 : ℝ)^3203
        have hw : |(-271876589/2000000000 : ℝ)|=(271876589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599440291/1000000000 : ℝ)|^4227 ≤ (50896889516741/100000000000000 : ℝ)^3203
        have hw : |(599440291/1000000000 : ℝ)|=(599440291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s0_6 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174829383/10000000000 : ℝ)*x 0 + (374650057/625000000 : ℝ)*x 1 + (-679692269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174829383/10000000000 : ℝ)^4227 ≤ (20960349594677/50000000000000 : ℝ)^3203 := by
    have hnat : (5174829383 : ℕ)^4227*50000000000000^3203 ≤ 20960349594677^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174829383 10000000000 20960349594677 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374650057/625000000 : ℝ)^4227 ≤ (50896867128701/100000000000000 : ℝ)^3203 := by
    have hnat : (374650057 : ℕ)^4227*100000000000000^3203 ≤ 50896867128701^3203*625000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374650057 625000000 50896867128701 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679692269/5000000000 : ℝ)^4227 ≤ (7182433668749/100000000000000 : ℝ)^3203 := by
    have hnat : (679692269 : ℕ)^4227*100000000000000^3203 ≤ 7182433668749^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679692269 5000000000 7182433668749 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174829383/10000000000 : ℝ), (374650057/625000000 : ℝ), (-679692269/5000000000 : ℝ)] ![(20960349594677/50000000000000 : ℝ), (50896867128701/100000000000000 : ℝ), (7182433668749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174829383/10000000000 : ℝ)|^4227 ≤ (20960349594677/50000000000000 : ℝ)^3203
        have hw : |(5174829383/10000000000 : ℝ)|=(5174829383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(374650057/625000000 : ℝ)|^4227 ≤ (50896867128701/100000000000000 : ℝ)^3203
        have hw : |(374650057/625000000 : ℝ)|=(374650057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-679692269/5000000000 : ℝ)|^4227 ≤ (7182433668749/100000000000000 : ℝ)^3203
        have hw : |(-679692269/5000000000 : ℝ)|=(679692269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s0_7 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (420131613/1000000000 : ℝ)*x 0 + (173743651/312500000 : ℝ)*x 1 + (3183035359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420131613/1000000000 : ℝ)^4227 ≤ (1592031146527/5000000000000 : ℝ)^3203 := by
    have hnat : (420131613 : ℕ)^4227*5000000000000^3203 ≤ 1592031146527^3203*1000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420131613 1000000000 1592031146527 5000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173743651/312500000 : ℝ)^4227 ≤ (4608442651253/10000000000000 : ℝ)^3203 := by
    have hnat : (173743651 : ℕ)^4227*10000000000000^3203 ≤ 4608442651253^3203*312500000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173743651 312500000 4608442651253 10000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183035359/10000000000 : ℝ)^4227 ≤ (11037475267189/50000000000000 : ℝ)^3203 := by
    have hnat : (3183035359 : ℕ)^4227*50000000000000^3203 ≤ 11037475267189^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183035359 10000000000 11037475267189 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420131613/1000000000 : ℝ), (173743651/312500000 : ℝ), (3183035359/10000000000 : ℝ)] ![(1592031146527/5000000000000 : ℝ), (4608442651253/10000000000000 : ℝ), (11037475267189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420131613/1000000000 : ℝ)|^4227 ≤ (1592031146527/5000000000000 : ℝ)^3203
        have hw : |(420131613/1000000000 : ℝ)|=(420131613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173743651/312500000 : ℝ)|^4227 ≤ (4608442651253/10000000000000 : ℝ)^3203
        have hw : |(173743651/312500000 : ℝ)|=(173743651/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183035359/10000000000 : ℝ)|^4227 ≤ (11037475267189/50000000000000 : ℝ)^3203
        have hw : |(3183035359/10000000000 : ℝ)|=(3183035359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1261_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (893/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5473/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8453/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8453 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8453*1^2048 ≤ 0^2048*1^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8453/2048 : ℝ) ≤ (569463561174447453/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8453 ≤ (569463561174447453/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8453*25000000000000000000^2048 ≤ 569463561174447453^2048*5^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 569463561174447453 25000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (569463561174447453/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8453 := by
      have hnat : (1 : ℕ)^2048*1^8453 ≤ 1^8453*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25569463561174447453/25000000000000000000 : ℝ) ≤ (10054718038125779/10000000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (25569463561174447453/25000000000000000000 : ℝ)^2048 ≤ (10054718038125779/10000000000000000 : ℝ)^8453 := by
      have hnat : (25569463561174447453 : ℕ)^2048*10000000000000000^8453 ≤ 10054718038125779^8453*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25569463561174447453 25000000000000000000 10054718038125779 10000000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054718038125779/10000000000000000 : ℝ)) (X := (25569463561174447453/25000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13069463561174447453/12500000000000000000 : ℝ) ≤ (5054718038125779/5000000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (13069463561174447453/12500000000000000000 : ℝ)^2048 ≤ (5054718038125779/5000000000000000 : ℝ)^8453 := by
      have hnat : (13069463561174447453 : ℕ)^2048*5000000000000000^8453 ≤ 5054718038125779^8453*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13069463561174447453 12500000000000000000 5054718038125779 5000000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054718038125779/5000000000000000 : ℝ)) (X := (13069463561174447453/12500000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54718038125779/4000000000000000 : ℝ)*(0 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(54718038125779/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(569463561174447453/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54718038125779/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8453/2048 : ℝ) := by
    rw [show (1 : ℝ)+(54718038125779/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054718038125779/10000000000000000 : ℝ) by norm_num, show 1+(569463561174447453/25000000000000000000 : ℝ)+(0 : ℝ)=(25569463561174447453/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(569463561174447453/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54718038125779/4000000000000000 : ℝ)*(2/5 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(54718038125779/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054718038125779/5000000000000000 : ℝ) by norm_num, show 1+2*(569463561174447453/25000000000000000000 : ℝ)=(13069463561174447453/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54718038125779/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54718038125779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54718038125779/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54718038125779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54718038125779/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54718038125779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-927355807/5000000000 : ℝ)*X 0 0+(3013616631/5000000000 : ℝ)*X 0 1+(599416947/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5510089049/10000000000 : ℝ)*X 1 0+(-1279225151/5000000000 : ℝ)*X 1 1+(2397667773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2755044541/5000000000 : ℝ)*X 2 0+(2397667773/5000000000 : ℝ)*X 2 1+(-2558450259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((209576667/500000000 : ℝ)*X 0 0+(3116193403/10000000000 : ℝ)*X 0 1+(1406088951/2500000000 : ℝ)*X 0 2+(209576667/500000000 : ℝ)*X 1 0+(3116193403/10000000000 : ℝ)*X 1 1+(1406088951/2500000000 : ℝ)*X 1 2+(209576667/500000000 : ℝ)*X 2 0+(3116193403/10000000000 : ℝ)*X 2 1+(1406088951/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929757647/5000000000 : ℝ)*X 0 0+(1206761737/2500000000 : ℝ)*X 0 1+(1198880099/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646853541/1250000000 : ℝ)*X 1 0+(-271876589/2000000000 : ℝ)*X 1 1+(599440291/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174829383/10000000000 : ℝ)*X 2 0+(374650057/625000000 : ℝ)*X 2 1+(-679692269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((420131613/1000000000 : ℝ)*X 0 0+(173743651/312500000 : ℝ)*X 0 1+(3183035359/10000000000 : ℝ)*X 0 2+(420131613/1000000000 : ℝ)*X 1 0+(173743651/312500000 : ℝ)*X 1 1+(3183035359/10000000000 : ℝ)*X 1 2+(420131613/1000000000 : ℝ)*X 2 0+(173743651/312500000 : ℝ)*X 2 1+(3183035359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (367098978053759231061147/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41272889/50000000000000 : ℝ)*(base1) + (1786011181/100000000000000 : ℝ)*(base19) + (1790872853/100000000000000 : ℝ)*(base23) + (202209159/100000000000000 : ℝ)*(upper3) + (107158547/50000000000000 : ℝ)*(upper5) + (151308836863377/25000000000000 : ℝ)*(major0) + (151308836863377/25000000000000 : ℝ)*(major1) + (151308836863377/25000000000000 : ℝ)*(major2) + (811761063967011/100000000000000 : ℝ)*(sp0) + (405882455477571/50000000000000 : ℝ)*(sp1) + (81176490609347/10000000000000 : ℝ)*(sp2) + (79740182141837/20000000000000 : ℝ)*(sp3) + (5715545089/100000000000000 : ℝ)*(sp4) + (172497067/6250000000000 : ℝ)*(sp7) + (199351876604017/50000000000000 : ℝ)*(f.failure) + (811766696966323/100000000000000 : ℝ)*(f.sum) + (94899952304317/50000000000000000000000000000 : ℝ)*base66 + (552967106604317/100000000000000000000000000000 : ℝ)*base68 + (337422666795683/100000000000000000000000000000 : ℝ)*base69 + (409595757104317/100000000000000000000000000000 : ℝ)*base72 + (180534914054317/50000000000000000000000000000 : ℝ)*base74 + (363474847304317/100000000000000000000000000000 : ℝ)*base76 + (35001215304317/100000000000000000000000000000 : ℝ)*base78 + (783539743204317/100000000000000000000000000000 : ℝ)*base80 + (99294971795683/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3465399/1000000000000000000000 : ℝ)*base90 + (3465399/1000000000000000000000 : ℝ)*base92 + (3465399/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46014539435850134061477/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53298929/25000000000000 : ℝ)*(base1) + (771711203/100000000000000 : ℝ)*(base19) + (910061801/100000000000000 : ℝ)*(base23) + (165086491/100000000000000 : ℝ)*(upper3) + (79836221934093/12500000000000 : ℝ)*(major0) + (79836221934093/12500000000000 : ℝ)*(major1) + (79836221934093/12500000000000 : ℝ)*(major2) + (1860694293/100000000000000 : ℝ)*(sp1) + (1300505001/100000000000000 : ℝ)*(sp2) + (417063903/100000000000000 : ℝ)*(sp3) + (856637509159457/100000000000000 : ℝ)*(sp4) + (171326932711649/20000000000000 : ℝ)*(sp5) + (856635085396939/100000000000000 : ℝ)*(sp6) + (420741502016687/100000000000000 : ℝ)*(sp7) + (210371066138153/50000000000000 : ℝ)*(f.failure) + (856637295963741/100000000000000 : ℝ)*(f.sum) + (14901882983447/25000000000000000000000000000 : ℝ)*base65 + (48980445833447/50000000000000000000000000000 : ℝ)*base67 + (150392689283447/50000000000000000000000000000 : ℝ)*base69 + (261560729933447/50000000000000000000000000000 : ℝ)*base71 + (3700445233447/25000000000000000000000000000 : ℝ)*base73 + (41892653633447/50000000000000000000000000000 : ℝ)*base75 + (343965929833447/50000000000000000000000000000 : ℝ)*base77 + (93356111933447/50000000000000000000000000000 : ℝ)*base79 + (31988077183447/25000000000000000000000000000 : ℝ)*base81 + (4217409/1000000000000000000000 : ℝ)*base89 + (4217409/1000000000000000000000 : ℝ)*base91 + (4217409/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1261_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (893/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5473/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1261_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1261_s1_0 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-102537111/500000000 : ℝ)*x 0 + (226834623/400000000 : ℝ)*x 1 + (5026220389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102537111/500000000 : ℝ)^4227 ≤ (12357449637967/100000000000000 : ℝ)^3203 := by
    have hnat : (102537111 : ℕ)^4227*100000000000000^3203 ≤ 12357449637967^3203*500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102537111 500000000 12357449637967 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226834623/400000000 : ℝ)^4227 ≤ (47303250137673/100000000000000 : ℝ)^3203 := by
    have hnat : (226834623 : ℕ)^4227*100000000000000^3203 ≤ 47303250137673^3203*400000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226834623 400000000 47303250137673 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026220389/10000000000 : ℝ)^4227 ≤ (40339300209467/100000000000000 : ℝ)^3203 := by
    have hnat : (5026220389 : ℕ)^4227*100000000000000^3203 ≤ 40339300209467^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026220389 10000000000 40339300209467 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102537111/500000000 : ℝ), (226834623/400000000 : ℝ), (5026220389/10000000000 : ℝ)] ![(12357449637967/100000000000000 : ℝ), (47303250137673/100000000000000 : ℝ), (40339300209467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102537111/500000000 : ℝ)|^4227 ≤ (12357449637967/100000000000000 : ℝ)^3203
        have hw : |(-102537111/500000000 : ℝ)|=(102537111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226834623/400000000 : ℝ)|^4227 ≤ (47303250137673/100000000000000 : ℝ)^3203
        have hw : |(226834623/400000000 : ℝ)|=(226834623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026220389/10000000000 : ℝ)|^4227 ≤ (40339300209467/100000000000000 : ℝ)^3203
        have hw : |(5026220389/10000000000 : ℝ)|=(5026220389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s1_1 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412626813/10000000000 : ℝ)*x 0 + (-2396596549/10000000000 : ℝ)*x 1 + (5026220761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412626813/10000000000 : ℝ)^4227 ≤ (44481412972127/100000000000000 : ℝ)^3203 := by
    have hnat : (5412626813 : ℕ)^4227*100000000000000^3203 ≤ 44481412972127^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412626813 10000000000 44481412972127 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2396596549/10000000000 : ℝ)^4227 ≤ (948705179487/6250000000000 : ℝ)^3203 := by
    have hnat : (2396596549 : ℕ)^4227*6250000000000^3203 ≤ 948705179487^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396596549 10000000000 948705179487 6250000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026220761/10000000000 : ℝ)^4227 ≤ (10084826037387/25000000000000 : ℝ)^3203 := by
    have hnat : (5026220761 : ℕ)^4227*25000000000000^3203 ≤ 10084826037387^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026220761 10000000000 10084826037387 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412626813/10000000000 : ℝ), (-2396596549/10000000000 : ℝ), (5026220761/10000000000 : ℝ)] ![(44481412972127/100000000000000 : ℝ), (948705179487/6250000000000 : ℝ), (10084826037387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412626813/10000000000 : ℝ)|^4227 ≤ (44481412972127/100000000000000 : ℝ)^3203
        have hw : |(5412626813/10000000000 : ℝ)|=(5412626813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2396596549/10000000000 : ℝ)|^4227 ≤ (948705179487/6250000000000 : ℝ)^3203
        have hw : |(-2396596549/10000000000 : ℝ)|=(2396596549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026220761/10000000000 : ℝ)|^4227 ≤ (10084826037387/25000000000000 : ℝ)^3203
        have hw : |(5026220761/10000000000 : ℝ)|=(5026220761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s1_2 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135315679/250000000 : ℝ)*x 0 + (5026220521/10000000000 : ℝ)*x 1 + (-1198298201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135315679/250000000 : ℝ)^4227 ≤ (22240708367741/50000000000000 : ℝ)^3203 := by
    have hnat : (135315679 : ℕ)^4227*50000000000000^3203 ≤ 22240708367741^3203*250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135315679 250000000 22240708367741 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5026220521/10000000000 : ℝ)^4227 ≤ (1008482540189/2500000000000 : ℝ)^3203 := by
    have hnat : (5026220521 : ℕ)^4227*2500000000000^3203 ≤ 1008482540189^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026220521 10000000000 1008482540189 2500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198298201/5000000000 : ℝ)^4227 ≤ (15179281643083/100000000000000 : ℝ)^3203 := by
    have hnat : (1198298201 : ℕ)^4227*100000000000000^3203 ≤ 15179281643083^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198298201 5000000000 15179281643083 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135315679/250000000 : ℝ), (5026220521/10000000000 : ℝ), (-1198298201/5000000000 : ℝ)] ![(22240708367741/50000000000000 : ℝ), (1008482540189/2500000000000 : ℝ), (15179281643083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135315679/250000000 : ℝ)|^4227 ≤ (22240708367741/50000000000000 : ℝ)^3203
        have hw : |(135315679/250000000 : ℝ)|=(135315679/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5026220521/10000000000 : ℝ)|^4227 ≤ (1008482540189/2500000000000 : ℝ)^3203
        have hw : |(5026220521/10000000000 : ℝ)|=(5026220521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1198298201/5000000000 : ℝ)|^4227 ≤ (15179281643083/100000000000000 : ℝ)^3203
        have hw : |(-1198298201/5000000000 : ℝ)|=(1198298201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s1_3 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307202177/10000000000 : ℝ)*x 0 + (3698859143/10000000000 : ℝ)*x 1 + (5011367321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307202177/10000000000 : ℝ)^4227 ≤ (4112987520873/12500000000000 : ℝ)^3203 := by
    have hnat : (4307202177 : ℕ)^4227*12500000000000^3203 ≤ 4112987520873^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307202177 10000000000 4112987520873 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3698859143/10000000000 : ℝ)^4227 ≤ (6728510801877/25000000000000 : ℝ)^3203 := by
    have hnat : (3698859143 : ℕ)^4227*25000000000000^3203 ≤ 6728510801877^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698859143 10000000000 6728510801877 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5011367321/10000000000 : ℝ)^4227 ≤ (20091028305397/50000000000000 : ℝ)^3203 := by
    have hnat : (5011367321 : ℕ)^4227*50000000000000^3203 ≤ 20091028305397^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011367321 10000000000 20091028305397 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307202177/10000000000 : ℝ), (3698859143/10000000000 : ℝ), (5011367321/10000000000 : ℝ)] ![(4112987520873/12500000000000 : ℝ), (6728510801877/25000000000000 : ℝ), (20091028305397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307202177/10000000000 : ℝ)|^4227 ≤ (4112987520873/12500000000000 : ℝ)^3203
        have hw : |(4307202177/10000000000 : ℝ)|=(4307202177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3698859143/10000000000 : ℝ)|^4227 ≤ (6728510801877/25000000000000 : ℝ)^3203
        have hw : |(3698859143/10000000000 : ℝ)|=(3698859143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5011367321/10000000000 : ℝ)|^4227 ≤ (20091028305397/50000000000000 : ℝ)^3203
        have hw : |(5011367321/10000000000 : ℝ)|=(5011367321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s1_4 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-128212263/625000000 : ℝ)*x 0 + (5034625533/10000000000 : ℝ)*x 1 + (5662301829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128212263/625000000 : ℝ)^4227 ≤ (1236265061579/10000000000000 : ℝ)^3203 := by
    have hnat : (128212263 : ℕ)^4227*10000000000000^3203 ≤ 1236265061579^3203*625000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128212263 625000000 1236265061579 10000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5034625533/10000000000 : ℝ)^4227 ≤ (40428348037709/100000000000000 : ℝ)^3203 := by
    have hnat : (5034625533 : ℕ)^4227*100000000000000^3203 ≤ 40428348037709^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5034625533 10000000000 40428348037709 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5662301829/10000000000 : ℝ)^4227 ≤ (47209001337369/100000000000000 : ℝ)^3203 := by
    have hnat : (5662301829 : ℕ)^4227*100000000000000^3203 ≤ 47209001337369^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662301829 10000000000 47209001337369 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128212263/625000000 : ℝ), (5034625533/10000000000 : ℝ), (5662301829/10000000000 : ℝ)] ![(1236265061579/10000000000000 : ℝ), (40428348037709/100000000000000 : ℝ), (47209001337369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128212263/625000000 : ℝ)|^4227 ≤ (1236265061579/10000000000000 : ℝ)^3203
        have hw : |(-128212263/625000000 : ℝ)|=(128212263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5034625533/10000000000 : ℝ)|^4227 ≤ (40428348037709/100000000000000 : ℝ)^3203
        have hw : |(5034625533/10000000000 : ℝ)|=(5034625533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5662301829/10000000000 : ℝ)|^4227 ≤ (47209001337369/100000000000000 : ℝ)^3203
        have hw : |(5662301829/10000000000 : ℝ)|=(5662301829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s1_5 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5246399613/10000000000 : ℝ)*x 0 + (-1760515017/10000000000 : ℝ)*x 1 + (2831151127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246399613/10000000000 : ℝ)^4227 ≤ (1707500969829/4000000000000 : ℝ)^3203 := by
    have hnat : (5246399613 : ℕ)^4227*4000000000000^3203 ≤ 1707500969829^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246399613 10000000000 1707500969829 4000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1760515017/10000000000 : ℝ)^4227 ≤ (5051734867507/50000000000000 : ℝ)^3203 := by
    have hnat : (1760515017 : ℕ)^4227*50000000000000^3203 ≤ 5051734867507^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760515017 10000000000 5051734867507 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831151127/5000000000 : ℝ)^4227 ≤ (47209006013601/100000000000000 : ℝ)^3203 := by
    have hnat : (2831151127 : ℕ)^4227*100000000000000^3203 ≤ 47209006013601^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831151127 5000000000 47209006013601 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246399613/10000000000 : ℝ), (-1760515017/10000000000 : ℝ), (2831151127/5000000000 : ℝ)] ![(1707500969829/4000000000000 : ℝ), (5051734867507/50000000000000 : ℝ), (47209006013601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246399613/10000000000 : ℝ)|^4227 ≤ (1707500969829/4000000000000 : ℝ)^3203
        have hw : |(5246399613/10000000000 : ℝ)|=(5246399613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1760515017/10000000000 : ℝ)|^4227 ≤ (5051734867507/50000000000000 : ℝ)^3203
        have hw : |(-1760515017/10000000000 : ℝ)|=(1760515017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2831151127/5000000000 : ℝ)|^4227 ≤ (47209006013601/100000000000000 : ℝ)^3203
        have hw : |(2831151127/5000000000 : ℝ)|=(2831151127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s1_6 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524639953/1000000000 : ℝ)*x 0 + (5662301977/10000000000 : ℝ)*x 1 + (-352103107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524639953/1000000000 : ℝ)^4227 ≤ (5335940419311/12500000000000 : ℝ)^3203 := by
    have hnat : (524639953 : ℕ)^4227*12500000000000^3203 ≤ 5335940419311^3203*1000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524639953 1000000000 5335940419311 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5662301977/10000000000 : ℝ)^4227 ≤ (23604501482899/50000000000000 : ℝ)^3203 := by
    have hnat : (5662301977 : ℕ)^4227*50000000000000^3203 ≤ 23604501482899^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662301977 10000000000 23604501482899 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352103107/2000000000 : ℝ)^4227 ≤ (10103473658173/100000000000000 : ℝ)^3203 := by
    have hnat : (352103107 : ℕ)^4227*100000000000000^3203 ≤ 10103473658173^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352103107 2000000000 10103473658173 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524639953/1000000000 : ℝ), (5662301977/10000000000 : ℝ), (-352103107/2000000000 : ℝ)] ![(5335940419311/12500000000000 : ℝ), (23604501482899/50000000000000 : ℝ), (10103473658173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524639953/1000000000 : ℝ)|^4227 ≤ (5335940419311/12500000000000 : ℝ)^3203
        have hw : |(524639953/1000000000 : ℝ)|=(524639953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5662301977/10000000000 : ℝ)|^4227 ≤ (23604501482899/50000000000000 : ℝ)^3203
        have hw : |(5662301977/10000000000 : ℝ)|=(5662301977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352103107/2000000000 : ℝ)|^4227 ≤ (10103473658173/100000000000000 : ℝ)^3203
        have hw : |(-352103107/2000000000 : ℝ)|=(352103107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s1_7 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308533469/10000000000 : ℝ)*x 0 + (78035227/156250000 : ℝ)*x 1 + (1858147757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308533469/10000000000 : ℝ)^4227 ≤ (32917322320687/100000000000000 : ℝ)^3203 := by
    have hnat : (4308533469 : ℕ)^4227*100000000000000^3203 ≤ 32917322320687^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308533469 10000000000 32917322320687 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78035227/156250000 : ℝ)^4227 ≤ (8000214969093/20000000000000 : ℝ)^3203 := by
    have hnat : (78035227 : ℕ)^4227*20000000000000^3203 ≤ 8000214969093^3203*156250000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78035227 156250000 8000214969093 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858147757/5000000000 : ℝ)^4227 ≤ (5416320563803/20000000000000 : ℝ)^3203 := by
    have hnat : (1858147757 : ℕ)^4227*20000000000000^3203 ≤ 5416320563803^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858147757 5000000000 5416320563803 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308533469/10000000000 : ℝ), (78035227/156250000 : ℝ), (1858147757/5000000000 : ℝ)] ![(32917322320687/100000000000000 : ℝ), (8000214969093/20000000000000 : ℝ), (5416320563803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308533469/10000000000 : ℝ)|^4227 ≤ (32917322320687/100000000000000 : ℝ)^3203
        have hw : |(4308533469/10000000000 : ℝ)|=(4308533469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78035227/156250000 : ℝ)|^4227 ≤ (8000214969093/20000000000000 : ℝ)^3203
        have hw : |(78035227/156250000 : ℝ)|=(78035227/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1858147757/5000000000 : ℝ)|^4227 ≤ (5416320563803/20000000000000 : ℝ)^3203
        have hw : |(1858147757/5000000000 : ℝ)|=(1858147757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1261_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5473/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (629/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19919/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5473/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5473/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5473/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5473/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5473/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5473/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (893/100000 : ℝ) ^ (8453/2048 : ℝ) ≤ (34854548703/10000000000000000000 : ℝ) := by
    have hpowers : (893/100000 : ℝ)^8453 ≤ (34854548703/10000000000000000000 : ℝ)^2048 := by
      have hnat : (893 : ℕ)^8453*10000000000000000000^2048 ≤ 34854548703^2048*100000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        893 100000 34854548703 10000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (893/100000 : ℝ)) (X := (34854548703/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5473/20000 : ℝ) ^ (8453/2048 : ℝ) ≤ (475397843044999107/100000000000000000000 : ℝ) := by
    have hpowers : (5473/20000 : ℝ)^8453 ≤ (475397843044999107/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5473 : ℕ)^8453*100000000000000000000^2048 ≤ 475397843044999107^2048*20000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5473 20000 475397843044999107 100000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5473/20000 : ℝ)) (X := (475397843044999107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000034854548703/5000000000000000000 : ℝ) ≤ (500000000844459/500000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (5000000034854548703/5000000000000000000 : ℝ)^2048 ≤ (500000000844459/500000000000000 : ℝ)^8453 := by
      have hnat : (5000000034854548703 : ℕ)^2048*500000000000000^8453 ≤ 500000000844459^8453*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000034854548703 5000000000000000000 500000000844459 500000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000844459/500000000000000 : ℝ)) (X := (5000000034854548703/5000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100475398191590486137/100000000000000000000 : ℝ) ≤ (400459892011893/400000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (100475398191590486137/100000000000000000000 : ℝ)^2048 ≤ (400459892011893/400000000000000 : ℝ)^8453 := by
      have hnat : (100475398191590486137 : ℕ)^2048*400000000000000^8453 ≤ 400459892011893^8453*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100475398191590486137 100000000000000000000 400459892011893 400000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400459892011893/400000000000000 : ℝ)) (X := (100475398191590486137/100000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50475397843044999107/50000000000000000000 : ℝ) ≤ (1002299458370547/1000000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (50475397843044999107/50000000000000000000 : ℝ)^2048 ≤ (1002299458370547/1000000000000000 : ℝ)^8453 := by
      have hnat : (50475397843044999107 : ℕ)^2048*1000000000000000^8453 ≤ 1002299458370547^8453*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50475397843044999107 50000000000000000000 1002299458370547 1000000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002299458370547/1000000000000000 : ℝ)) (X := (50475397843044999107/50000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(34854548703/10000000000000000000 : ℝ) ≤ ((8823315543297447533/8824000000000000000 : ℝ)+2*(766485560543/176480000000000 : ℝ)*(893/100000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (8823315543297447533/8824000000000000000 : ℝ)+2*(766485560543/176480000000000 : ℝ)*(893/100000 : ℝ)=(500000000844459/500000000000000 : ℝ) by norm_num, show 1+2*(34854548703/10000000000000000000 : ℝ)=(5000000034854548703/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(475397843044999107/100000000000000000000 : ℝ)+(34854548703/10000000000000000000 : ℝ) ≤ ((8823315543297447533/8824000000000000000 : ℝ)+(766485560543/176480000000000 : ℝ)*((5473/20000 : ℝ)+(893/100000 : ℝ)))^(8453/2048 : ℝ) := by
    rw [show (8823315543297447533/8824000000000000000 : ℝ)+(766485560543/176480000000000 : ℝ)*((5473/20000 : ℝ)+(893/100000 : ℝ))=(400459892011893/400000000000000 : ℝ) by norm_num, show 1+(475397843044999107/100000000000000000000 : ℝ)+(34854548703/10000000000000000000 : ℝ)=(100475398191590486137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(475397843044999107/100000000000000000000 : ℝ) ≤ ((8823315543297447533/8824000000000000000 : ℝ)+2*(766485560543/176480000000000 : ℝ)*(5473/20000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (8823315543297447533/8824000000000000000 : ℝ)+2*(766485560543/176480000000000 : ℝ)*(5473/20000 : ℝ)=(1002299458370547/1000000000000000 : ℝ) by norm_num, show 1+2*(475397843044999107/100000000000000000000 : ℝ)=(50475397843044999107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8823315543297447533/8824000000000000000 : ℝ)*(X 1 0+X 2 0)+(766485560543/176480000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (893/100000 : ℝ)) (hi := (5473/20000 : ℝ)) (c := (8823315543297447533/8824000000000000000 : ℝ)) (alpha := (766485560543/176480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8823315543297447533/8824000000000000000 : ℝ)*(X 0 1+X 2 1)+(766485560543/176480000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (893/100000 : ℝ)) (hi := (5473/20000 : ℝ)) (c := (8823315543297447533/8824000000000000000 : ℝ)) (alpha := (766485560543/176480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8823315543297447533/8824000000000000000 : ℝ)*(X 0 2+X 1 2)+(766485560543/176480000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (893/100000 : ℝ)) (hi := (5473/20000 : ℝ)) (c := (8823315543297447533/8824000000000000000 : ℝ)) (alpha := (766485560543/176480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-102537111/500000000 : ℝ)*X 0 0+(226834623/400000000 : ℝ)*X 0 1+(5026220389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5412626813/10000000000 : ℝ)*X 1 0+(-2396596549/10000000000 : ℝ)*X 1 1+(5026220761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((135315679/250000000 : ℝ)*X 2 0+(5026220521/10000000000 : ℝ)*X 2 1+(-1198298201/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307202177/10000000000 : ℝ)*X 0 0+(3698859143/10000000000 : ℝ)*X 0 1+(5011367321/10000000000 : ℝ)*X 0 2+(4307202177/10000000000 : ℝ)*X 1 0+(3698859143/10000000000 : ℝ)*X 1 1+(5011367321/10000000000 : ℝ)*X 1 2+(4307202177/10000000000 : ℝ)*X 2 0+(3698859143/10000000000 : ℝ)*X 2 1+(5011367321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-128212263/625000000 : ℝ)*X 0 0+(5034625533/10000000000 : ℝ)*X 0 1+(5662301829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246399613/10000000000 : ℝ)*X 1 0+(-1760515017/10000000000 : ℝ)*X 1 1+(2831151127/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((524639953/1000000000 : ℝ)*X 2 0+(5662301977/10000000000 : ℝ)*X 2 1+(-352103107/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308533469/10000000000 : ℝ)*X 0 0+(78035227/156250000 : ℝ)*X 0 1+(1858147757/5000000000 : ℝ)*X 0 2+(4308533469/10000000000 : ℝ)*X 1 0+(78035227/156250000 : ℝ)*X 1 1+(1858147757/5000000000 : ℝ)*X 1 2+(4308533469/10000000000 : ℝ)*X 2 0+(78035227/156250000 : ℝ)*X 2 1+(1858147757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (465262656266415641000400621/110300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12643753/50000000000000 : ℝ)*(base1) + (498985327/50000000000000 : ℝ)*(base19) + (274355113/25000000000000 : ℝ)*(base23) + (95788501/100000000000000 : ℝ)*(upper3) + (176839771/100000000000000 : ℝ)*(upper5) + (578290140009779/50000000000000 : ℝ)*(major0) + (578290140009779/50000000000000 : ℝ)*(major1) + (578290140009779/50000000000000 : ℝ)*(major2) + (19390583580583/1250000000000 : ℝ)*(sp0) + (1551252668213641/100000000000000 : ℝ)*(sp1) + (1551252568763843/100000000000000 : ℝ)*(sp2) + (761903459367931/100000000000000 : ℝ)*(sp3) + (175125629/2500000000000 : ℝ)*(sp4) + (653718833/20000000000000 : ℝ)*(sp7) + (380953376624801/50000000000000 : ℝ)*(f.failure) + (310250733236859/20000000000000 : ℝ)*(f.sum) + (2821556575907/4412000000000000000000000000 : ℝ)*base66 + (1409277237300324793/441200000000000000000000000000000 : ℝ)*base68 + (2377269379906075207/441200000000000000000000000000000 : ℝ)*base69 + (1401975276706724793/441200000000000000000000000000000 : ℝ)*base72 + (11542259531731/4412000000000000000000000000 : ℝ)*base74 + (1853856356775124793/441200000000000000000000000000000 : ℝ)*base76 + (589646549083124793/441200000000000000000000000000000 : ℝ)*base78 + (2113253276127924793/441200000000000000000000000000000 : ℝ)*base80 + (14167706750697/4412000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1954553/1000000000000000000000 : ℝ)*base89 + (1954553/1000000000000000000000 : ℝ)*base91 + (1954553/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1818811912581731099737769691/220600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3885261/10000000000000 : ℝ)*(base1) + (100055153/6250000000000 : ℝ)*(base19) + (1541804103/100000000000000 : ℝ)*(base23) + (13561061/6250000000000 : ℝ)*(upper3) + (90126997/50000000000000 : ℝ)*(upper5) + (593918853377903/50000000000000 : ℝ)*(major0) + (593918853377903/50000000000000 : ℝ)*(major1) + (593918853377903/50000000000000 : ℝ)*(major2) + (8224542959/100000000000000 : ℝ)*(sp1) + (894426917/12500000000000 : ℝ)*(sp2) + (796588668923779/50000000000000 : ℝ)*(sp4) + (79658373678477/5000000000000 : ℝ)*(sp5) + (398292150443877/25000000000000 : ℝ)*(sp6) + (156499560167203/20000000000000 : ℝ)*(sp7) + (6259982717509/800000000000 : ℝ)*(f.failure) + (398294324748737/25000000000000 : ℝ)*(f.sum) + (5235392697277/4412000000000000000000000000 : ℝ)*base65 + (5004007157130286701/441200000000000000000000000000000 : ℝ)*base68 + (2337392573799886701/441200000000000000000000000000000 : ℝ)*base70 + (3108042539115886701/441200000000000000000000000000000 : ℝ)*base72 + (4136940242741/4412000000000000000000000000 : ℝ)*base73 + (3856590377332286701/441200000000000000000000000000000 : ℝ)*base76 + (4922472824011486701/441200000000000000000000000000000 : ℝ)*base78 + (579384847799886701/441200000000000000000000000000000 : ℝ)*base80 + (18208557119833/4412000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (58877/16000000000000000000 : ℝ)*base89 + (58877/16000000000000000000 : ℝ)*base91 + (58877/16000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1261_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5473/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (629/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19919/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1261_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1261_s2_0 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097838623/10000000000 : ℝ)*x 0 + (171549709/312500000 : ℝ)*x 1 + (5177443561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097838623/10000000000 : ℝ)^4227 ≤ (318333561363/2500000000000 : ℝ)^3203 := by
    have hnat : (2097838623 : ℕ)^4227*2500000000000^3203 ≤ 318333561363^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097838623 10000000000 318333561363 2500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171549709/312500000 : ℝ)^4227 ≤ (9063601716503/20000000000000 : ℝ)^3203 := by
    have hnat : (171549709 : ℕ)^4227*20000000000000^3203 ≤ 9063601716503^3203*312500000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171549709 312500000 9063601716503 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177443561/10000000000 : ℝ)^4227 ≤ (5243581118093/12500000000000 : ℝ)^3203 := by
    have hnat : (5177443561 : ℕ)^4227*12500000000000^3203 ≤ 5243581118093^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177443561 10000000000 5243581118093 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097838623/10000000000 : ℝ), (171549709/312500000 : ℝ), (5177443561/10000000000 : ℝ)] ![(318333561363/2500000000000 : ℝ), (9063601716503/20000000000000 : ℝ), (5243581118093/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097838623/10000000000 : ℝ)|^4227 ≤ (318333561363/2500000000000 : ℝ)^3203
        have hw : |(-2097838623/10000000000 : ℝ)|=(2097838623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171549709/312500000 : ℝ)|^4227 ≤ (9063601716503/20000000000000 : ℝ)^3203
        have hw : |(171549709/312500000 : ℝ)|=(171549709/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177443561/10000000000 : ℝ)|^4227 ≤ (5243581118093/12500000000000 : ℝ)^3203
        have hw : |(5177443561/10000000000 : ℝ)|=(5177443561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s2_1 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167778757/312500000 : ℝ)*x 0 + (-1129711493/5000000000 : ℝ)*x 1 + (258872187/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167778757/312500000 : ℝ)^4227 ≤ (8801602052051/20000000000000 : ℝ)^3203 := by
    have hnat : (167778757 : ℕ)^4227*20000000000000^3203 ≤ 8801602052051^3203*312500000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167778757 312500000 8801602052051 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129711493/5000000000 : ℝ)^4227 ≤ (14043338868083/100000000000000 : ℝ)^3203 := by
    have hnat : (1129711493 : ℕ)^4227*100000000000000^3203 ≤ 14043338868083^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129711493 5000000000 14043338868083 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258872187/500000000 : ℝ)^4227 ≤ (5243581357337/12500000000000 : ℝ)^3203 := by
    have hnat : (258872187 : ℕ)^4227*12500000000000^3203 ≤ 5243581357337^3203*500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258872187 500000000 5243581357337 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167778757/312500000 : ℝ), (-1129711493/5000000000 : ℝ), (258872187/500000000 : ℝ)] ![(8801602052051/20000000000000 : ℝ), (14043338868083/100000000000000 : ℝ), (5243581357337/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167778757/312500000 : ℝ)|^4227 ≤ (8801602052051/20000000000000 : ℝ)^3203
        have hw : |(167778757/312500000 : ℝ)|=(167778757/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129711493/5000000000 : ℝ)|^4227 ≤ (14043338868083/100000000000000 : ℝ)^3203
        have hw : |(-1129711493/5000000000 : ℝ)|=(1129711493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258872187/500000000 : ℝ)|^4227 ≤ (5243581357337/12500000000000 : ℝ)^3203
        have hw : |(258872187/500000000 : ℝ)|=(258872187/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s2_2 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368920149/10000000000 : ℝ)*x 0 + (1035488753/2000000000 : ℝ)*x 1 + (-564855763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368920149/10000000000 : ℝ)^4227 ≤ (11002002362239/25000000000000 : ℝ)^3203 := by
    have hnat : (5368920149 : ℕ)^4227*25000000000000^3203 ≤ 11002002362239^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368920149 10000000000 11002002362239 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035488753/2000000000 : ℝ)^4227 ≤ (5243581390751/12500000000000 : ℝ)^3203 := by
    have hnat : (1035488753 : ℕ)^4227*12500000000000^3203 ≤ 5243581390751^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035488753 2000000000 5243581390751 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564855763/2500000000 : ℝ)^4227 ≤ (14043339409451/100000000000000 : ℝ)^3203 := by
    have hnat : (564855763 : ℕ)^4227*100000000000000^3203 ≤ 14043339409451^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564855763 2500000000 14043339409451 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368920149/10000000000 : ℝ), (1035488753/2000000000 : ℝ), (-564855763/2500000000 : ℝ)] ![(11002002362239/25000000000000 : ℝ), (5243581390751/12500000000000 : ℝ), (14043339409451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368920149/10000000000 : ℝ)|^4227 ≤ (11002002362239/25000000000000 : ℝ)^3203
        have hw : |(5368920149/10000000000 : ℝ)|=(5368920149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035488753/2000000000 : ℝ)|^4227 ≤ (5243581390751/12500000000000 : ℝ)^3203
        have hw : |(1035488753/2000000000 : ℝ)|=(1035488753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-564855763/2500000000 : ℝ)|^4227 ≤ (14043339409451/100000000000000 : ℝ)^3203
        have hw : |(-564855763/2500000000 : ℝ)|=(564855763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s2_3 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271235933/625000000 : ℝ)*x 0 + (806645497/2000000000 : ℝ)*x 1 + (4668763269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271235933/625000000 : ℝ)^4227 ≤ (6646536073019/20000000000000 : ℝ)^3203 := by
    have hnat : (271235933 : ℕ)^4227*20000000000000^3203 ≤ 6646536073019^3203*625000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271235933 625000000 6646536073019 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806645497/2000000000 : ℝ)^4227 ≤ (1206812424121/4000000000000 : ℝ)^3203 := by
    have hnat : (806645497 : ℕ)^4227*4000000000000^3203 ≤ 1206812424121^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806645497 2000000000 1206812424121 4000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4668763269/10000000000 : ℝ)^4227 ≤ (36597009019647/100000000000000 : ℝ)^3203 := by
    have hnat : (4668763269 : ℕ)^4227*100000000000000^3203 ≤ 36597009019647^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4668763269 10000000000 36597009019647 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271235933/625000000 : ℝ), (806645497/2000000000 : ℝ), (4668763269/10000000000 : ℝ)] ![(6646536073019/20000000000000 : ℝ), (1206812424121/4000000000000 : ℝ), (36597009019647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271235933/625000000 : ℝ)|^4227 ≤ (6646536073019/20000000000000 : ℝ)^3203
        have hw : |(271235933/625000000 : ℝ)|=(271235933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806645497/2000000000 : ℝ)|^4227 ≤ (1206812424121/4000000000000 : ℝ)^3203
        have hw : |(806645497/2000000000 : ℝ)|=(806645497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4668763269/10000000000 : ℝ)|^4227 ≤ (36597009019647/100000000000000 : ℝ)^3203
        have hw : |(4668763269/10000000000 : ℝ)|=(4668763269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s2_4 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-65559787/312500000 : ℝ)*x 0 + (5179424131/10000000000 : ℝ)*x 1 + (1097518357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65559787/312500000 : ℝ)^4227 ≤ (12733939709587/100000000000000 : ℝ)^3203 := by
    have hnat : (65559787 : ℕ)^4227*100000000000000^3203 ≤ 12733939709587^3203*312500000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65559787 312500000 12733939709587 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179424131/10000000000 : ℝ)^4227 ≤ (262311421367/625000000000 : ℝ)^3203 := by
    have hnat : (5179424131 : ℕ)^4227*625000000000^3203 ≤ 262311421367^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179424131 10000000000 262311421367 625000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097518357/2000000000 : ℝ)^4227 ≤ (4529623285863/10000000000000 : ℝ)^3203 := by
    have hnat : (1097518357 : ℕ)^4227*10000000000000^3203 ≤ 4529623285863^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097518357 2000000000 4529623285863 10000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65559787/312500000 : ℝ), (5179424131/10000000000 : ℝ), (1097518357/2000000000 : ℝ)] ![(12733939709587/100000000000000 : ℝ), (262311421367/625000000000 : ℝ), (4529623285863/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65559787/312500000 : ℝ)|^4227 ≤ (12733939709587/100000000000000 : ℝ)^3203
        have hw : |(-65559787/312500000 : ℝ)|=(65559787/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179424131/10000000000 : ℝ)|^4227 ≤ (262311421367/625000000000 : ℝ)^3203
        have hw : |(5179424131/10000000000 : ℝ)|=(5179424131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097518357/2000000000 : ℝ)|^4227 ≤ (4529623285863/10000000000000 : ℝ)^3203
        have hw : |(1097518357/2000000000 : ℝ)|=(1097518357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s2_5 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289112587/10000000000 : ℝ)*x 0 + (-121829667/625000000 : ℝ)*x 1 + (5487591829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289112587/10000000000 : ℝ)^4227 ≤ (5393345371881/12500000000000 : ℝ)^3203 := by
    have hnat : (5289112587 : ℕ)^4227*12500000000000^3203 ≤ 5393345371881^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289112587 10000000000 5393345371881 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121829667/625000000 : ℝ)^4227 ≤ (11557003667267/100000000000000 : ℝ)^3203 := by
    have hnat : (121829667 : ℕ)^4227*100000000000000^3203 ≤ 11557003667267^3203*625000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121829667 625000000 11557003667267 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487591829/10000000000 : ℝ)^4227 ≤ (45296233337931/100000000000000 : ℝ)^3203 := by
    have hnat : (5487591829 : ℕ)^4227*100000000000000^3203 ≤ 45296233337931^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487591829 10000000000 45296233337931 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289112587/10000000000 : ℝ), (-121829667/625000000 : ℝ), (5487591829/10000000000 : ℝ)] ![(5393345371881/12500000000000 : ℝ), (11557003667267/100000000000000 : ℝ), (45296233337931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289112587/10000000000 : ℝ)|^4227 ≤ (5393345371881/12500000000000 : ℝ)^3203
        have hw : |(5289112587/10000000000 : ℝ)|=(5289112587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121829667/625000000 : ℝ)|^4227 ≤ (11557003667267/100000000000000 : ℝ)^3203
        have hw : |(-121829667/625000000 : ℝ)|=(121829667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487591829/10000000000 : ℝ)|^4227 ≤ (45296233337931/100000000000000 : ℝ)^3203
        have hw : |(5487591829/10000000000 : ℝ)|=(5487591829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s2_6 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644556357/5000000000 : ℝ)*x 0 + (274379597/500000000 : ℝ)*x 1 + (-974637171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644556357/5000000000 : ℝ)^4227 ≤ (43146764342287/100000000000000 : ℝ)^3203 := by
    have hnat : (2644556357 : ℕ)^4227*100000000000000^3203 ≤ 43146764342287^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644556357 5000000000 43146764342287 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274379597/500000000 : ℝ)^4227 ≤ (11324058636769/25000000000000 : ℝ)^3203 := by
    have hnat : (274379597 : ℕ)^4227*25000000000000^3203 ≤ 11324058636769^3203*500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274379597 500000000 11324058636769 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974637171/5000000000 : ℝ)^4227 ≤ (2889250271309/25000000000000 : ℝ)^3203 := by
    have hnat : (974637171 : ℕ)^4227*25000000000000^3203 ≤ 2889250271309^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974637171 5000000000 2889250271309 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644556357/5000000000 : ℝ), (274379597/500000000 : ℝ), (-974637171/5000000000 : ℝ)] ![(43146764342287/100000000000000 : ℝ), (11324058636769/25000000000000 : ℝ), (2889250271309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644556357/5000000000 : ℝ)|^4227 ≤ (43146764342287/100000000000000 : ℝ)^3203
        have hw : |(2644556357/5000000000 : ℝ)|=(2644556357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274379597/500000000 : ℝ)|^4227 ≤ (11324058636769/25000000000000 : ℝ)^3203
        have hw : |(274379597/500000000 : ℝ)|=(274379597/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974637171/5000000000 : ℝ)|^4227 ≤ (2889250271309/25000000000000 : ℝ)^3203
        have hw : |(-974637171/5000000000 : ℝ)|=(974637171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s2_7 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339926289/10000000000 : ℝ)*x 0 + (2332365639/5000000000 : ℝ)*x 1 + (4037296389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339926289/10000000000 : ℝ)^4227 ≤ (8308552501847/25000000000000 : ℝ)^3203 := by
    have hnat : (4339926289 : ℕ)^4227*25000000000000^3203 ≤ 8308552501847^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339926289 10000000000 8308552501847 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2332365639/5000000000 : ℝ)^4227 ≤ (7311060986233/20000000000000 : ℝ)^3203 := by
    have hnat : (2332365639 : ℕ)^4227*20000000000000^3203 ≤ 7311060986233^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2332365639 5000000000 7311060986233 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4037296389/10000000000 : ℝ)^4227 ≤ (30210485042881/100000000000000 : ℝ)^3203 := by
    have hnat : (4037296389 : ℕ)^4227*100000000000000^3203 ≤ 30210485042881^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037296389 10000000000 30210485042881 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339926289/10000000000 : ℝ), (2332365639/5000000000 : ℝ), (4037296389/10000000000 : ℝ)] ![(8308552501847/25000000000000 : ℝ), (7311060986233/20000000000000 : ℝ), (30210485042881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339926289/10000000000 : ℝ)|^4227 ≤ (8308552501847/25000000000000 : ℝ)^3203
        have hw : |(4339926289/10000000000 : ℝ)|=(4339926289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2332365639/5000000000 : ℝ)|^4227 ≤ (7311060986233/20000000000000 : ℝ)^3203
        have hw : |(2332365639/5000000000 : ℝ)|=(2332365639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4037296389/10000000000 : ℝ)|^4227 ≤ (30210485042881/100000000000000 : ℝ)^3203
        have hw : |(4037296389/10000000000 : ℝ)|=(4037296389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1261_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19919/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (629/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1197/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8087/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19919/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (629/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19919/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (629/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19919/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (629/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19919/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (629/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19919/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (629/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19919/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (629/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (629/10000 : ℝ) ^ (8453/2048 : ℝ) ≤ (55013710152203/5000000000000000000 : ℝ) := by
    have hpowers : (629/10000 : ℝ)^8453 ≤ (55013710152203/5000000000000000000 : ℝ)^2048 := by
      have hnat : (629 : ℕ)^8453*5000000000000000000^2048 ≤ 55013710152203^2048*10000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        629 10000 55013710152203 5000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (629/10000 : ℝ)) (X := (55013710152203/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (19919/100000 : ℝ) ^ (8453/2048 : ℝ) ≤ (64082257035580423/50000000000000000000 : ℝ) := by
    have hpowers : (19919/100000 : ℝ)^8453 ≤ (64082257035580423/50000000000000000000 : ℝ)^2048 := by
      have hnat : (19919 : ℕ)^8453*50000000000000000000^2048 ≤ 64082257035580423^2048*100000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19919 100000 64082257035580423 50000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19919/100000 : ℝ)) (X := (64082257035580423/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500055013710152203/2500000000000000000 : ℝ) ≤ (1250006664328587/1250000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (2500055013710152203/2500000000000000000 : ℝ)^2048 ≤ (1250006664328587/1250000000000000 : ℝ)^8453 := by
      have hnat : (2500055013710152203 : ℕ)^2048*1250000000000000^8453 ≤ 1250006664328587^8453*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500055013710152203 2500000000000000000 1250006664328587 1250000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250006664328587/1250000000000000 : ℝ)) (X := (2500055013710152203/2500000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50064632394137102453/50000000000000000000 : ℝ) ≤ (10003130305638603/10000000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (50064632394137102453/50000000000000000000 : ℝ)^2048 ≤ (10003130305638603/10000000000000000 : ℝ)^8453 := by
      have hnat : (50064632394137102453 : ℕ)^2048*10000000000000000^8453 ≤ 10003130305638603^8453*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064632394137102453 50000000000000000000 10003130305638603 10000000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003130305638603/10000000000000000 : ℝ)) (X := (50064632394137102453/50000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25064082257035580423/25000000000000000000 : ℝ) ≤ (1000620729664851/1000000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (25064082257035580423/25000000000000000000 : ℝ)^2048 ≤ (1000620729664851/1000000000000000 : ℝ)^8453 := by
      have hnat : (25064082257035580423 : ℕ)^2048*1000000000000000^8453 ≤ 1000620729664851^8453*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25064082257035580423 25000000000000000000 1000620729664851 1000000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000620729664851/1000000000000000 : ℝ)) (X := (25064082257035580423/25000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(55013710152203/5000000000000000000 : ℝ) ≤ ((11354334839847488977/11357500000000000000 : ℝ)+2*(1025663669969/454300000000000 : ℝ)*(629/10000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (11354334839847488977/11357500000000000000 : ℝ)+2*(1025663669969/454300000000000 : ℝ)*(629/10000 : ℝ)=(1250006664328587/1250000000000000 : ℝ) by norm_num, show 1+2*(55013710152203/5000000000000000000 : ℝ)=(2500055013710152203/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64082257035580423/50000000000000000000 : ℝ)+(55013710152203/5000000000000000000 : ℝ) ≤ ((11354334839847488977/11357500000000000000 : ℝ)+(1025663669969/454300000000000 : ℝ)*((19919/100000 : ℝ)+(629/10000 : ℝ)))^(8453/2048 : ℝ) := by
    rw [show (11354334839847488977/11357500000000000000 : ℝ)+(1025663669969/454300000000000 : ℝ)*((19919/100000 : ℝ)+(629/10000 : ℝ))=(10003130305638603/10000000000000000 : ℝ) by norm_num, show 1+(64082257035580423/50000000000000000000 : ℝ)+(55013710152203/5000000000000000000 : ℝ)=(50064632394137102453/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64082257035580423/50000000000000000000 : ℝ) ≤ ((11354334839847488977/11357500000000000000 : ℝ)+2*(1025663669969/454300000000000 : ℝ)*(19919/100000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (11354334839847488977/11357500000000000000 : ℝ)+2*(1025663669969/454300000000000 : ℝ)*(19919/100000 : ℝ)=(1000620729664851/1000000000000000 : ℝ) by norm_num, show 1+2*(64082257035580423/50000000000000000000 : ℝ)=(25064082257035580423/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11354334839847488977/11357500000000000000 : ℝ)*(X 1 0+X 2 0)+(1025663669969/454300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (629/10000 : ℝ)) (hi := (19919/100000 : ℝ)) (c := (11354334839847488977/11357500000000000000 : ℝ)) (alpha := (1025663669969/454300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11354334839847488977/11357500000000000000 : ℝ)*(X 0 1+X 2 1)+(1025663669969/454300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (629/10000 : ℝ)) (hi := (19919/100000 : ℝ)) (c := (11354334839847488977/11357500000000000000 : ℝ)) (alpha := (1025663669969/454300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11354334839847488977/11357500000000000000 : ℝ)*(X 0 2+X 1 2)+(1025663669969/454300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (629/10000 : ℝ)) (hi := (19919/100000 : ℝ)) (c := (11354334839847488977/11357500000000000000 : ℝ)) (alpha := (1025663669969/454300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2097838623/10000000000 : ℝ)*X 0 0+(171549709/312500000 : ℝ)*X 0 1+(5177443561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167778757/312500000 : ℝ)*X 1 0+(-1129711493/5000000000 : ℝ)*X 1 1+(258872187/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368920149/10000000000 : ℝ)*X 2 0+(1035488753/2000000000 : ℝ)*X 2 1+(-564855763/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271235933/625000000 : ℝ)*X 0 0+(806645497/2000000000 : ℝ)*X 0 1+(4668763269/10000000000 : ℝ)*X 0 2+(271235933/625000000 : ℝ)*X 1 0+(806645497/2000000000 : ℝ)*X 1 1+(4668763269/10000000000 : ℝ)*X 1 2+(271235933/625000000 : ℝ)*X 2 0+(806645497/2000000000 : ℝ)*X 2 1+(4668763269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-65559787/312500000 : ℝ)*X 0 0+(5179424131/10000000000 : ℝ)*X 0 1+(1097518357/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289112587/10000000000 : ℝ)*X 1 0+(-121829667/625000000 : ℝ)*X 1 1+(5487591829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644556357/5000000000 : ℝ)*X 2 0+(274379597/500000000 : ℝ)*X 2 1+(-974637171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339926289/10000000000 : ℝ)*X 0 0+(2332365639/5000000000 : ℝ)*X 0 1+(4037296389/10000000000 : ℝ)*X 0 2+(4339926289/10000000000 : ℝ)*X 1 0+(2332365639/5000000000 : ℝ)*X 1 1+(4037296389/10000000000 : ℝ)*X 1 2+(4339926289/10000000000 : ℝ)*X 2 0+(2332365639/5000000000 : ℝ)*X 2 1+(4037296389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1950914879114198862757035177/567875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (527004463/100000000000000 : ℝ)*(base19) + (362849/78125000000 : ℝ)*(base23) + (9559513/100000000000000 : ℝ)*(lower2) + (20102947/20000000000000 : ℝ)*(upper3) + (29540519/100000000000000 : ℝ)*(upper5) + (2388557172526867/100000000000000 : ℝ)*(major0) + (2388557172526867/100000000000000 : ℝ)*(major1) + (2388557172526867/100000000000000 : ℝ)*(major2) + (1601812892039331/50000000000000 : ℝ)*(sp0) + (640726411933063/20000000000000 : ℝ)*(sp1) + (1601816061111529/50000000000000 : ℝ)*(sp2) + (1573478281079687/100000000000000 : ℝ)*(sp3) + (1360518223/20000000000000 : ℝ)*(sp4) + (3362788753/100000000000000 : ℝ)*(sp7) + (39337041096711/2500000000000 : ℝ)*(f.failure) + (1601816293334889/50000000000000 : ℝ)*(f.sum) + (34204999301141/11357500000000000000000000000 : ℝ)*base66 + (3504488505409420059/1135750000000000000000000000000000 : ℝ)*base67 + (4874309394519170059/1135750000000000000000000000000000 : ℝ)*base69 + (13320553634592829941/1135750000000000000000000000000000 : ℝ)*base72 + (16290555048869/11357500000000000000000000000 : ℝ)*base73 + (3489912897618079941/1135750000000000000000000000000000 : ℝ)*base76 + (4681772326474329941/1135750000000000000000000000000000 : ℝ)*base78 + (640360531592329941/1135750000000000000000000000000000 : ℝ)*base80 + (16185110425763/22715000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (256783/50000000000000000000 : ℝ)*base89 + (256783/50000000000000000000 : ℝ)*base91 + (256783/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19917260690127432661763991/4812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244965109/20000000000000 : ℝ)*(base19) + (1506977963/100000000000000 : ℝ)*(base23) + (28422949/50000000000000 : ℝ)*(upper2) + (7252331/4000000000000 : ℝ)*(upper3) + (76828447/100000000000000 : ℝ)*(upper5) + (1209694188190133/50000000000000 : ℝ)*(major0) + (1209694188190133/50000000000000 : ℝ)*(major1) + (1209694188190133/50000000000000 : ℝ)*(major2) + (6217367631/50000000000000 : ℝ)*(sp1) + (9423626327/50000000000000 : ℝ)*(sp2) + (648996932464147/20000000000000 : ℝ)*(sp4) + (405621375344991/12500000000000 : ℝ)*(sp5) + (1622482154045059/50000000000000 : ℝ)*(sp6) + (1593791952484737/100000000000000 : ℝ)*(sp7) + (1593791952484737/100000000000000 : ℝ)*(f.failure) + (648996932464147/20000000000000 : ℝ)*(f.sum) + (62511011872641/22715000000000000000000000000 : ℝ)*base66 + (4035803400912036059/567875000000000000000000000000000 : ℝ)*base68 + (5447606806645911059/567875000000000000000000000000000 : ℝ)*base70 + (8303862884234286059/567875000000000000000000000000000 : ℝ)*base72 + (7186357205021/5678750000000000000000000000 : ℝ)*base73 + (1881025969624786059/567875000000000000000000000000000 : ℝ)*base76 + (1696145067207036059/567875000000000000000000000000000 : ℝ)*base78 + (8488962705303911059/567875000000000000000000000000000 : ℝ)*base80 + (151696952171481/22715000000000000000000000000 : ℝ)*base82 + (25484761/2000000000000000000000 : ℝ)*base89 + (25484761/2000000000000000000000 : ℝ)*base91 + (25484761/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1261_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19919/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (629/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1197/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8087/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1261_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1261_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1197/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8087/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1261_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1261_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1261_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1197/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8087/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1261_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
