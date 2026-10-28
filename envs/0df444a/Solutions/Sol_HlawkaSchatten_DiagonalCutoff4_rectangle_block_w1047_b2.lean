-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1047_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:52:03.605571+00:00
-- url     : https://prove2.me/submissions/37b91dc5-6178-4880-bc39-ef3759de604a

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
theorem support_rectangle_w1047_s6_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-442621199/2000000000 : ℝ)*x 0 + (5395308933/10000000000 : ℝ)*x 1 + (82242353/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442621199/2000000000 : ℝ)^515 ≤ (6719425212307/50000000000000 : ℝ)^387 := by
    have hnat : (442621199 : ℕ)^515*50000000000000^387 ≤ 6719425212307^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442621199 2000000000 6719425212307 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395308933/10000000000 : ℝ)^515 ≤ (10998181842061/25000000000000 : ℝ)^387 := by
    have hnat : (5395308933 : ℕ)^515*25000000000000^387 ≤ 10998181842061^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395308933 10000000000 10998181842061 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82242353/156250000 : ℝ)^515 ≤ (5321052774637/12500000000000 : ℝ)^387 := by
    have hnat : (82242353 : ℕ)^515*12500000000000^387 ≤ 5321052774637^387*156250000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82242353 156250000 5321052774637 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442621199/2000000000 : ℝ), (5395308933/10000000000 : ℝ), (82242353/156250000 : ℝ)] ![(6719425212307/50000000000000 : ℝ), (10998181842061/25000000000000 : ℝ), (5321052774637/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442621199/2000000000 : ℝ)|^515 ≤ (6719425212307/50000000000000 : ℝ)^387
        have hw : |(-442621199/2000000000 : ℝ)|=(442621199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395308933/10000000000 : ℝ)|^515 ≤ (10998181842061/25000000000000 : ℝ)^387
        have hw : |(5395308933/10000000000 : ℝ)|=(5395308933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82242353/156250000 : ℝ)|^515 ≤ (5321052774637/12500000000000 : ℝ)^387
        have hw : |(82242353/156250000 : ℝ)|=(82242353/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s6_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672586971/5000000000 : ℝ)*x 0 + (-569997629/2500000000 : ℝ)*x 1 + (5263510579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672586971/5000000000 : ℝ)^515 ≤ (21724780742461/50000000000000 : ℝ)^387 := by
    have hnat : (2672586971 : ℕ)^515*50000000000000^387 ≤ 21724780742461^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672586971 5000000000 21724780742461 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569997629/2500000000 : ℝ)^515 ≤ (6991008219373/50000000000000 : ℝ)^387 := by
    have hnat : (569997629 : ℕ)^515*50000000000000^387 ≤ 6991008219373^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569997629 2500000000 6991008219373 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263510579/10000000000 : ℝ)^515 ≤ (8513684411437/20000000000000 : ℝ)^387 := by
    have hnat : (5263510579 : ℕ)^515*20000000000000^387 ≤ 8513684411437^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263510579 10000000000 8513684411437 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672586971/5000000000 : ℝ), (-569997629/2500000000 : ℝ), (5263510579/10000000000 : ℝ)] ![(21724780742461/50000000000000 : ℝ), (6991008219373/50000000000000 : ℝ), (8513684411437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672586971/5000000000 : ℝ)|^515 ≤ (21724780742461/50000000000000 : ℝ)^387
        have hw : |(2672586971/5000000000 : ℝ)|=(2672586971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-569997629/2500000000 : ℝ)|^515 ≤ (6991008219373/50000000000000 : ℝ)^387
        have hw : |(-569997629/2500000000 : ℝ)|=(569997629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263510579/10000000000 : ℝ)|^515 ≤ (8513684411437/20000000000000 : ℝ)^387
        have hw : |(5263510579/10000000000 : ℝ)|=(5263510579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s6_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672586893/5000000000 : ℝ)*x 0 + (1052702137/2000000000 : ℝ)*x 1 + (-284998823/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672586893/5000000000 : ℝ)^515 ≤ (43449559797419/100000000000000 : ℝ)^387 := by
    have hnat : (2672586893 : ℕ)^515*100000000000000^387 ≤ 43449559797419^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672586893 5000000000 43449559797419 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052702137/2000000000 : ℝ)^515 ≤ (42568423197997/100000000000000 : ℝ)^387 := by
    have hnat : (1052702137 : ℕ)^515*100000000000000^387 ≤ 42568423197997^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052702137 2000000000 42568423197997 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284998823/1250000000 : ℝ)^515 ≤ (13982016993681/100000000000000 : ℝ)^387 := by
    have hnat : (284998823 : ℕ)^515*100000000000000^387 ≤ 13982016993681^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284998823 1250000000 13982016993681 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672586893/5000000000 : ℝ), (1052702137/2000000000 : ℝ), (-284998823/1250000000 : ℝ)] ![(43449559797419/100000000000000 : ℝ), (42568423197997/100000000000000 : ℝ), (13982016993681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672586893/5000000000 : ℝ)|^515 ≤ (43449559797419/100000000000000 : ℝ)^387
        have hw : |(2672586893/5000000000 : ℝ)|=(2672586893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052702137/2000000000 : ℝ)|^515 ≤ (42568423197997/100000000000000 : ℝ)^387
        have hw : |(1052702137/2000000000 : ℝ)|=(1052702137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284998823/1250000000 : ℝ)|^515 ≤ (13982016993681/100000000000000 : ℝ)^387
        have hw : |(-284998823/1250000000 : ℝ)|=(284998823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s6_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4378200833/10000000000 : ℝ)*x 0 + (2125729253/5000000000 : ℝ)*x 1 + (901758231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378200833/10000000000 : ℝ)^515 ≤ (33316123008711/100000000000000 : ℝ)^387 := by
    have hnat : (4378200833 : ℕ)^515*100000000000000^387 ≤ 33316123008711^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378200833 10000000000 33316123008711 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125729253/5000000000 : ℝ)^515 ≤ (16019432036761/50000000000000 : ℝ)^387 := by
    have hnat : (2125729253 : ℕ)^515*50000000000000^387 ≤ 16019432036761^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125729253 5000000000 16019432036761 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901758231/2000000000 : ℝ)^515 ≤ (866125322649/2500000000000 : ℝ)^387 := by
    have hnat : (901758231 : ℕ)^515*2500000000000^387 ≤ 866125322649^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901758231 2000000000 866125322649 2500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378200833/10000000000 : ℝ), (2125729253/5000000000 : ℝ), (901758231/2000000000 : ℝ)] ![(33316123008711/100000000000000 : ℝ), (16019432036761/50000000000000 : ℝ), (866125322649/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378200833/10000000000 : ℝ)|^515 ≤ (33316123008711/100000000000000 : ℝ)^387
        have hw : |(4378200833/10000000000 : ℝ)|=(4378200833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125729253/5000000000 : ℝ)|^515 ≤ (16019432036761/50000000000000 : ℝ)^387
        have hw : |(2125729253/5000000000 : ℝ)|=(2125729253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901758231/2000000000 : ℝ)|^515 ≤ (866125322649/2500000000000 : ℝ)^387
        have hw : |(901758231/2000000000 : ℝ)|=(901758231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s6_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-221311127/1000000000 : ℝ)*x 0 + (5263843501/10000000000 : ℝ)*x 1 + (5394974801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221311127/1000000000 : ℝ)^515 ≤ (3359723262757/25000000000000 : ℝ)^387 := by
    have hnat : (221311127 : ℕ)^515*25000000000000^387 ≤ 3359723262757^387*1000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221311127 1000000000 3359723262757 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263843501/10000000000 : ℝ)^515 ≤ (8514401025537/20000000000000 : ℝ)^387 := by
    have hnat : (5263843501 : ℕ)^515*20000000000000^387 ≤ 8514401025537^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263843501 10000000000 8514401025537 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394974801/10000000000 : ℝ)^515 ≤ (4398910181359/10000000000000 : ℝ)^387 := by
    have hnat : (5394974801 : ℕ)^515*10000000000000^387 ≤ 4398910181359^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394974801 10000000000 4398910181359 10000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221311127/1000000000 : ℝ), (5263843501/10000000000 : ℝ), (5394974801/10000000000 : ℝ)] ![(3359723262757/25000000000000 : ℝ), (8514401025537/20000000000000 : ℝ), (4398910181359/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221311127/1000000000 : ℝ)|^515 ≤ (3359723262757/25000000000000 : ℝ)^387
        have hw : |(-221311127/1000000000 : ℝ)|=(221311127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263843501/10000000000 : ℝ)|^515 ≤ (8514401025537/20000000000000 : ℝ)^387
        have hw : |(5263843501/10000000000 : ℝ)|=(5263843501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394974801/10000000000 : ℝ)|^515 ≤ (4398910181359/10000000000000 : ℝ)^387
        have hw : |(5394974801/10000000000 : ℝ)|=(5394974801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s6_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312027099/10000000000 : ℝ)*x 0 + (-2148526357/10000000000 : ℝ)*x 1 + (5394974851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312027099/10000000000 : ℝ)^515 ≤ (10772842396263/25000000000000 : ℝ)^387 := by
    have hnat : (5312027099 : ℕ)^515*25000000000000^387 ≤ 10772842396263^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312027099 10000000000 10772842396263 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148526357/10000000000 : ℝ)^515 ≤ (12919528044433/100000000000000 : ℝ)^387 := by
    have hnat : (2148526357 : ℕ)^515*100000000000000^387 ≤ 12919528044433^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148526357 10000000000 12919528044433 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394974851/10000000000 : ℝ)^515 ≤ (21994551178059/50000000000000 : ℝ)^387 := by
    have hnat : (5394974851 : ℕ)^515*50000000000000^387 ≤ 21994551178059^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394974851 10000000000 21994551178059 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312027099/10000000000 : ℝ), (-2148526357/10000000000 : ℝ), (5394974851/10000000000 : ℝ)] ![(10772842396263/25000000000000 : ℝ), (12919528044433/100000000000000 : ℝ), (21994551178059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312027099/10000000000 : ℝ)|^515 ≤ (10772842396263/25000000000000 : ℝ)^387
        have hw : |(5312027099/10000000000 : ℝ)|=(5312027099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148526357/10000000000 : ℝ)|^515 ≤ (12919528044433/100000000000000 : ℝ)^387
        have hw : |(-2148526357/10000000000 : ℝ)|=(2148526357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394974851/10000000000 : ℝ)|^515 ≤ (21994551178059/50000000000000 : ℝ)^387
        have hw : |(5394974851/10000000000 : ℝ)|=(5394974851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s6_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (664003387/1250000000 : ℝ)*x 0 + (2697487423/5000000000 : ℝ)*x 1 + (-67141449/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664003387/1250000000 : ℝ)^515 ≤ (43091369552667/100000000000000 : ℝ)^387 := by
    have hnat : (664003387 : ℕ)^515*100000000000000^387 ≤ 43091369552667^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664003387 1250000000 43091369552667 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697487423/5000000000 : ℝ)^515 ≤ (8797820460373/20000000000000 : ℝ)^387 := by
    have hnat : (2697487423 : ℕ)^515*20000000000000^387 ≤ 8797820460373^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697487423 5000000000 8797820460373 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67141449/312500000 : ℝ)^515 ≤ (2583905626491/20000000000000 : ℝ)^387 := by
    have hnat : (67141449 : ℕ)^515*20000000000000^387 ≤ 2583905626491^387*312500000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67141449 312500000 2583905626491 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664003387/1250000000 : ℝ), (2697487423/5000000000 : ℝ), (-67141449/312500000 : ℝ)] ![(43091369552667/100000000000000 : ℝ), (8797820460373/20000000000000 : ℝ), (2583905626491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664003387/1250000000 : ℝ)|^515 ≤ (43091369552667/100000000000000 : ℝ)^387
        have hw : |(664003387/1250000000 : ℝ)|=(664003387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697487423/5000000000 : ℝ)|^515 ≤ (8797820460373/20000000000000 : ℝ)^387
        have hw : |(2697487423/5000000000 : ℝ)|=(2697487423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67141449/312500000 : ℝ)|^515 ≤ (2583905626491/20000000000000 : ℝ)^387
        have hw : |(-67141449/312500000 : ℝ)|=(67141449/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s6_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4378211157/10000000000 : ℝ)*x 0 + (4508140989/10000000000 : ℝ)*x 1 + (170084439/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378211157/10000000000 : ℝ)^515 ≤ (1041132111053/3125000000000 : ℝ)^387 := by
    have hnat : (4378211157 : ℕ)^515*3125000000000^387 ≤ 1041132111053^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378211157 10000000000 1041132111053 3125000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508140989/10000000000 : ℝ)^515 ≤ (34638364909653/100000000000000 : ℝ)^387 := by
    have hnat : (4508140989 : ℕ)^515*100000000000000^387 ≤ 34638364909653^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508140989 10000000000 34638364909653 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170084439/400000000 : ℝ)^515 ≤ (3204540751667/10000000000000 : ℝ)^387 := by
    have hnat : (170084439 : ℕ)^515*10000000000000^387 ≤ 3204540751667^387*400000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170084439 400000000 3204540751667 10000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378211157/10000000000 : ℝ), (4508140989/10000000000 : ℝ), (170084439/400000000 : ℝ)] ![(1041132111053/3125000000000 : ℝ), (34638364909653/100000000000000 : ℝ), (3204540751667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378211157/10000000000 : ℝ)|^515 ≤ (1041132111053/3125000000000 : ℝ)^387
        have hw : |(4378211157/10000000000 : ℝ)|=(4378211157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508140989/10000000000 : ℝ)|^515 ≤ (34638364909653/100000000000000 : ℝ)^387
        have hw : |(4508140989/10000000000 : ℝ)|=(4508140989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170084439/400000000 : ℝ)|^515 ≤ (3204540751667/10000000000000 : ℝ)^387
        have hw : |(170084439/400000000 : ℝ)|=(170084439/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2803/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3501/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11167/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (369689367415339/2500000000000000000 : ℝ) := by
    have hpowers : (11167/100000 : ℝ)^8239 ≤ (369689367415339/2500000000000000000 : ℝ)^2048 := by
      have hnat : (11167 : ℕ)^8239*2500000000000000000^2048 ≤ 369689367415339^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11167 100000 369689367415339 2500000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11167/100000 : ℝ)) (X := (369689367415339/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14051/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (37262284895532167/100000000000000000000 : ℝ) := by
    have hpowers : (14051/100000 : ℝ)^8239 ≤ (37262284895532167/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14051 : ℕ)^8239*100000000000000000000^2048 ≤ 37262284895532167^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14051 100000 37262284895532167 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14051/100000 : ℝ)) (X := (37262284895532167/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250369689367415339/1250000000000000000 : ℝ) ≤ (10000735079217507/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (1250369689367415339/1250000000000000000 : ℝ)^2048 ≤ (10000735079217507/10000000000000000 : ℝ)^8239 := by
      have hnat : (1250369689367415339 : ℕ)^2048*10000000000000000^8239 ≤ 10000735079217507^8239*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250369689367415339 1250000000000000000 10000735079217507 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000735079217507/10000000000000000 : ℝ)) (X := (1250369689367415339/1250000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052049859592145727/100000000000000000000 : ℝ) ≤ (5000646785244871/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (100052049859592145727/100000000000000000000 : ℝ)^2048 ≤ (5000646785244871/5000000000000000 : ℝ)^8239 := by
      have hnat : (100052049859592145727 : ℕ)^2048*5000000000000000^8239 ≤ 5000646785244871^8239*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052049859592145727 100000000000000000000 5000646785244871 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000646785244871/5000000000000000 : ℝ)) (X := (100052049859592145727/100000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037262284895532167/50000000000000000000 : ℝ) ≤ (10001852061761977/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50037262284895532167/50000000000000000000 : ℝ)^2048 ≤ (10001852061761977/10000000000000000 : ℝ)^8239 := by
      have hnat : (50037262284895532167 : ℕ)^2048*10000000000000000^8239 ≤ 10001852061761977^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037262284895532167 50000000000000000000 10001852061761977 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001852061761977/10000000000000000 : ℝ)) (X := (50037262284895532167/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(369689367415339/2500000000000000000 : ℝ) ≤ ((14414823312194596849/14420000000000000000 : ℝ)+2*(111698254447/57680000000000 : ℝ)*(11167/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (14414823312194596849/14420000000000000000 : ℝ)+2*(111698254447/57680000000000 : ℝ)*(11167/100000 : ℝ)=(10000735079217507/10000000000000000 : ℝ) by norm_num, show 1+2*(369689367415339/2500000000000000000 : ℝ)=(1250369689367415339/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37262284895532167/100000000000000000000 : ℝ)+(369689367415339/2500000000000000000 : ℝ) ≤ ((14414823312194596849/14420000000000000000 : ℝ)+(111698254447/57680000000000 : ℝ)*((14051/100000 : ℝ)+(11167/100000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (14414823312194596849/14420000000000000000 : ℝ)+(111698254447/57680000000000 : ℝ)*((14051/100000 : ℝ)+(11167/100000 : ℝ))=(5000646785244871/5000000000000000 : ℝ) by norm_num, show 1+(37262284895532167/100000000000000000000 : ℝ)+(369689367415339/2500000000000000000 : ℝ)=(100052049859592145727/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37262284895532167/100000000000000000000 : ℝ) ≤ ((14414823312194596849/14420000000000000000 : ℝ)+2*(111698254447/57680000000000 : ℝ)*(14051/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (14414823312194596849/14420000000000000000 : ℝ)+2*(111698254447/57680000000000 : ℝ)*(14051/100000 : ℝ)=(10001852061761977/10000000000000000 : ℝ) by norm_num, show 1+2*(37262284895532167/100000000000000000000 : ℝ)=(50037262284895532167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14414823312194596849/14420000000000000000 : ℝ)*(X 1 0+X 2 0)+(111698254447/57680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (14414823312194596849/14420000000000000000 : ℝ)) (alpha := (111698254447/57680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14414823312194596849/14420000000000000000 : ℝ)*(X 0 1+X 2 1)+(111698254447/57680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (14414823312194596849/14420000000000000000 : ℝ)) (alpha := (111698254447/57680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14414823312194596849/14420000000000000000 : ℝ)*(X 0 2+X 1 2)+(111698254447/57680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (14414823312194596849/14420000000000000000 : ℝ)) (alpha := (111698254447/57680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-442621199/2000000000 : ℝ)*X 0 0+(5395308933/10000000000 : ℝ)*X 0 1+(82242353/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672586971/5000000000 : ℝ)*X 1 0+(-569997629/2500000000 : ℝ)*X 1 1+(5263510579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672586893/5000000000 : ℝ)*X 2 0+(1052702137/2000000000 : ℝ)*X 2 1+(-284998823/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378200833/10000000000 : ℝ)*X 0 0+(2125729253/5000000000 : ℝ)*X 0 1+(901758231/2000000000 : ℝ)*X 0 2+(4378200833/10000000000 : ℝ)*X 1 0+(2125729253/5000000000 : ℝ)*X 1 1+(901758231/2000000000 : ℝ)*X 1 2+(4378200833/10000000000 : ℝ)*X 2 0+(2125729253/5000000000 : ℝ)*X 2 1+(901758231/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-221311127/1000000000 : ℝ)*X 0 0+(5263843501/10000000000 : ℝ)*X 0 1+(5394974801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312027099/10000000000 : ℝ)*X 1 0+(-2148526357/10000000000 : ℝ)*X 1 1+(5394974851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664003387/1250000000 : ℝ)*X 2 0+(2697487423/5000000000 : ℝ)*X 2 1+(-67141449/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378211157/10000000000 : ℝ)*X 0 0+(4508140989/10000000000 : ℝ)*X 0 1+(170084439/400000000 : ℝ)*X 0 2+(4378211157/10000000000 : ℝ)*X 1 0+(4508140989/10000000000 : ℝ)*X 1 1+(170084439/400000000 : ℝ)*X 1 2+(4378211157/10000000000 : ℝ)*X 2 0+(4508140989/10000000000 : ℝ)*X 2 1+(170084439/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7250050419970995335744354823/721000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106535541/5000000000000 : ℝ)*(base19) + (362410971/20000000000000 : ℝ)*(base23) + (25981389/50000000000000 : ℝ)*(lower2) + (164535131/50000000000000 : ℝ)*(upper3) + (109231419/100000000000000 : ℝ)*(upper5) + (5736771880743903/100000000000000 : ℝ)*(major0) + (5736771880743903/100000000000000 : ℝ)*(major1) + (5736771880743903/100000000000000 : ℝ)*(major2) + (7587410976020907/100000000000000 : ℝ)*(sp0) + (7587459830667143/100000000000000 : ℝ)*(sp1) + (1896865037330777/25000000000000 : ℝ)*(sp2) + (971512285439283/25000000000000 : ℝ)*(sp3) + (199161551/390625000000 : ℝ)*(sp4) + (16161583879/50000000000000 : ℝ)*(sp7) + (388608146492489/10000000000000 : ℝ)*(f.failure) + (7587461961377963/100000000000000 : ℝ)*(f.sum) + (9011658927373/2884000000000000000000000000 : ℝ)*base65 + (4528504077561988353/1442000000000000000000000000000000 : ℝ)*base68 + (12008665040059988353/1442000000000000000000000000000000 : ℝ)*base70 + (15681800056295988353/1442000000000000000000000000000000 : ℝ)*base72 + (12276135561897/2884000000000000000000000000 : ℝ)*base73 + (7239557181733988353/1442000000000000000000000000000000 : ℝ)*base76 + (11768874196739988353/1442000000000000000000000000000000 : ℝ)*base78 + (5614984302867988353/1442000000000000000000000000000000 : ℝ)*base80 + (9256716240551/2884000000000000000000000000 : ℝ)*base82 + (1212909/500000000000000000000 : ℝ)*base89 + (1212909/500000000000000000000 : ℝ)*base91 + (1212909/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4201058671602187190023895691/721000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (558914943/50000000000000 : ℝ)*(base19) + (292391017/25000000000000 : ℝ)*(base23) + (27760849/20000000000000 : ℝ)*(upper3) + (1212013/4000000000000 : ℝ)*(lower4) + (166220283/100000000000000 : ℝ)*(upper5) + (5765868085286153/100000000000000 : ℝ)*(major0) + (5765868085286153/100000000000000 : ℝ)*(major1) + (5765868085286153/100000000000000 : ℝ)*(major2) + (31498212207/100000000000000 : ℝ)*(sp1) + (15669049289/50000000000000 : ℝ)*(sp2) + (7625944782063397/100000000000000 : ℝ)*(sp4) + (7625912166021303/100000000000000 : ℝ)*(sp5) + (7625912274400751/100000000000000 : ℝ)*(sp6) + (9764477985713/250000000000 : ℝ)*(sp7) + (9764477985713/250000000000 : ℝ)*(f.failure) + (7625944782063397/100000000000000 : ℝ)*(f.sum) + (294900961249/2884000000000000000000000000 : ℝ)*base66 + (16334188767339118103/1442000000000000000000000000000000 : ℝ)*base68 + (3916742185939118103/1442000000000000000000000000000000 : ℝ)*base70 + (5627310928087118103/1442000000000000000000000000000000 : ℝ)*base72 + (2939121183837/2884000000000000000000000000 : ℝ)*base74 + (19231352573682881897/1442000000000000000000000000000000 : ℝ)*base75 + (6349616026366881897/1442000000000000000000000000000000 : ℝ)*base77 + (2759752157857118103/1442000000000000000000000000000000 : ℝ)*base80 + (18598223789671/2884000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (40147/12500000000000000000 : ℝ)*base90 + (40147/12500000000000000000 : ℝ)*base92 + (40147/12500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1047_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1047_s7_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106575039/5000000000 : ℝ)*x 0 + (1078960279/2000000000 : ℝ)*x 1 + (82249831/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106575039/5000000000 : ℝ)^515 ≤ (13439206653179/100000000000000 : ℝ)^387 := by
    have hnat : (1106575039 : ℕ)^515*100000000000000^387 ≤ 13439206653179^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106575039 5000000000 13439206653179 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078960279/2000000000 : ℝ)^515 ≤ (8797444054463/20000000000000 : ℝ)^387 := by
    have hnat : (1078960279 : ℕ)^515*20000000000000^387 ≤ 8797444054463^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078960279 2000000000 8797444054463 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82249831/156250000 : ℝ)^515 ≤ (10643393265861/25000000000000 : ℝ)^387 := by
    have hnat : (82249831 : ℕ)^515*25000000000000^387 ≤ 10643393265861^387*156250000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82249831 156250000 10643393265861 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106575039/5000000000 : ℝ), (1078960279/2000000000 : ℝ), (82249831/156250000 : ℝ)] ![(13439206653179/100000000000000 : ℝ), (8797444054463/20000000000000 : ℝ), (10643393265861/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106575039/5000000000 : ℝ)|^515 ≤ (13439206653179/100000000000000 : ℝ)^387
        have hw : |(-1106575039/5000000000 : ℝ)|=(1106575039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078960279/2000000000 : ℝ)|^515 ≤ (8797444054463/20000000000000 : ℝ)^387
        have hw : |(1078960279/2000000000 : ℝ)|=(1078960279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82249831/156250000 : ℝ)|^515 ≤ (10643393265861/25000000000000 : ℝ)^387
        have hw : |(82249831/156250000 : ℝ)|=(82249831/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s7_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672523733/5000000000 : ℝ)*x 0 + (-2279526987/10000000000 : ℝ)*x 1 + (2631994581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672523733/5000000000 : ℝ)^515 ≤ (339439010613/781250000000 : ℝ)^387 := by
    have hnat : (2672523733 : ℕ)^515*781250000000^387 ≤ 339439010613^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672523733 5000000000 339439010613 781250000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279526987/10000000000 : ℝ)^515 ≤ (349455844897/2500000000000 : ℝ)^387 := by
    have hnat : (2279526987 : ℕ)^515*2500000000000^387 ≤ 349455844897^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279526987 10000000000 349455844897 2500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631994581/5000000000 : ℝ)^515 ≤ (5321696603333/12500000000000 : ℝ)^387 := by
    have hnat : (2631994581 : ℕ)^515*12500000000000^387 ≤ 5321696603333^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631994581 5000000000 5321696603333 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672523733/5000000000 : ℝ), (-2279526987/10000000000 : ℝ), (2631994581/5000000000 : ℝ)] ![(339439010613/781250000000 : ℝ), (349455844897/2500000000000 : ℝ), (5321696603333/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672523733/5000000000 : ℝ)|^515 ≤ (339439010613/781250000000 : ℝ)^387
        have hw : |(2672523733/5000000000 : ℝ)|=(2672523733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279526987/10000000000 : ℝ)|^515 ≤ (349455844897/2500000000000 : ℝ)^387
        have hw : |(-2279526987/10000000000 : ℝ)|=(2279526987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631994581/5000000000 : ℝ)|^515 ≤ (5321696603333/12500000000000 : ℝ)^387
        have hw : |(2631994581/5000000000 : ℝ)|=(2631994581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s7_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345047469/10000000000 : ℝ)*x 0 + (263199459/500000000 : ℝ)*x 1 + (-2279526959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345047469/10000000000 : ℝ)^515 ≤ (10862048347729/25000000000000 : ℝ)^387 := by
    have hnat : (5345047469 : ℕ)^515*25000000000000^387 ≤ 10862048347729^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345047469 10000000000 10862048347729 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263199459/500000000 : ℝ)^515 ≤ (42573573020393/100000000000000 : ℝ)^387 := by
    have hnat : (263199459 : ℕ)^515*100000000000000^387 ≤ 42573573020393^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263199459 500000000 42573573020393 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279526959/10000000000 : ℝ)^515 ≤ (436819798981/3125000000000 : ℝ)^387 := by
    have hnat : (2279526959 : ℕ)^515*3125000000000^387 ≤ 436819798981^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279526959 10000000000 436819798981 3125000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345047469/10000000000 : ℝ), (263199459/500000000 : ℝ), (-2279526959/10000000000 : ℝ)] ![(10862048347729/25000000000000 : ℝ), (42573573020393/100000000000000 : ℝ), (436819798981/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345047469/10000000000 : ℝ)|^515 ≤ (10862048347729/25000000000000 : ℝ)^387
        have hw : |(5345047469/10000000000 : ℝ)|=(5345047469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263199459/500000000 : ℝ)|^515 ≤ (42573573020393/100000000000000 : ℝ)^387
        have hw : |(263199459/500000000 : ℝ)|=(263199459/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2279526959/10000000000 : ℝ)|^515 ≤ (436819798981/3125000000000 : ℝ)^387
        have hw : |(-2279526959/10000000000 : ℝ)|=(2279526959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s7_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4378226171/10000000000 : ℝ)*x 0 + (4252417883/10000000000 : ℝ)*x 1 + (4507825083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378226171/10000000000 : ℝ)^515 ≤ (16658189795829/50000000000000 : ℝ)^387 := by
    have hnat : (4378226171 : ℕ)^515*50000000000000^387 ≤ 16658189795829^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378226171 10000000000 16658189795829 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252417883/10000000000 : ℝ)^515 ≤ (16024242766307/50000000000000 : ℝ)^387 := by
    have hnat : (4252417883 : ℕ)^515*50000000000000^387 ≤ 16024242766307^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252417883 10000000000 16024242766307 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507825083/10000000000 : ℝ)^515 ≤ (8658783715371/25000000000000 : ℝ)^387 := by
    have hnat : (4507825083 : ℕ)^515*25000000000000^387 ≤ 8658783715371^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507825083 10000000000 8658783715371 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378226171/10000000000 : ℝ), (4252417883/10000000000 : ℝ), (4507825083/10000000000 : ℝ)] ![(16658189795829/50000000000000 : ℝ), (16024242766307/50000000000000 : ℝ), (8658783715371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378226171/10000000000 : ℝ)|^515 ≤ (16658189795829/50000000000000 : ℝ)^387
        have hw : |(4378226171/10000000000 : ℝ)|=(4378226171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252417883/10000000000 : ℝ)|^515 ≤ (16024242766307/50000000000000 : ℝ)^387
        have hw : |(4252417883/10000000000 : ℝ)|=(4252417883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507825083/10000000000 : ℝ)|^515 ≤ (8658783715371/25000000000000 : ℝ)^387
        have hw : |(4507825083/10000000000 : ℝ)|=(4507825083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s7_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-88526211/400000000 : ℝ)*x 0 + (5264317201/10000000000 : ℝ)*x 1 + (5394472153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88526211/400000000 : ℝ)^515 ≤ (2687849729913/20000000000000 : ℝ)^387 := by
    have hnat : (88526211 : ℕ)^515*20000000000000^387 ≤ 2687849729913^387*400000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88526211 400000000 2687849729913 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264317201/10000000000 : ℝ)^515 ≤ (2128855172477/5000000000000 : ℝ)^387 := by
    have hnat : (5264317201 : ℕ)^515*5000000000000^387 ≤ 2128855172477^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264317201 10000000000 2128855172477 5000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394472153/10000000000 : ℝ)^515 ≤ (21991823944021/50000000000000 : ℝ)^387 := by
    have hnat : (5394472153 : ℕ)^515*50000000000000^387 ≤ 21991823944021^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394472153 10000000000 21991823944021 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88526211/400000000 : ℝ), (5264317201/10000000000 : ℝ), (5394472153/10000000000 : ℝ)] ![(2687849729913/20000000000000 : ℝ), (2128855172477/5000000000000 : ℝ), (21991823944021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88526211/400000000 : ℝ)|^515 ≤ (2687849729913/20000000000000 : ℝ)^387
        have hw : |(-88526211/400000000 : ℝ)|=(88526211/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264317201/10000000000 : ℝ)|^515 ≤ (2128855172477/5000000000000 : ℝ)^387
        have hw : |(5264317201/10000000000 : ℝ)|=(5264317201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394472153/10000000000 : ℝ)|^515 ≤ (21991823944021/50000000000000 : ℝ)^387
        have hw : |(5394472153/10000000000 : ℝ)|=(5394472153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s7_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656074397/5000000000 : ℝ)*x 0 + (-2149043967/10000000000 : ℝ)*x 1 + (1348618007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656074397/5000000000 : ℝ)^515 ≤ (2693292706159/6250000000000 : ℝ)^387 := by
    have hnat : (2656074397 : ℕ)^515*6250000000000^387 ≤ 2693292706159^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656074397 5000000000 2693292706159 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149043967/10000000000 : ℝ)^515 ≤ (6461835079881/50000000000000 : ℝ)^387 := by
    have hnat : (2149043967 : ℕ)^515*50000000000000^387 ≤ 6461835079881^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149043967 10000000000 6461835079881 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348618007/2500000000 : ℝ)^515 ≤ (10995911632941/25000000000000 : ℝ)^387 := by
    have hnat : (1348618007 : ℕ)^515*25000000000000^387 ≤ 10995911632941^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348618007 2500000000 10995911632941 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656074397/5000000000 : ℝ), (-2149043967/10000000000 : ℝ), (1348618007/2500000000 : ℝ)] ![(2693292706159/6250000000000 : ℝ), (6461835079881/50000000000000 : ℝ), (10995911632941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656074397/5000000000 : ℝ)|^515 ≤ (2693292706159/6250000000000 : ℝ)^387
        have hw : |(2656074397/5000000000 : ℝ)|=(2656074397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149043967/10000000000 : ℝ)|^515 ≤ (6461835079881/50000000000000 : ℝ)^387
        have hw : |(-2149043967/10000000000 : ℝ)|=(2149043967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348618007/2500000000 : ℝ)|^515 ≤ (10995911632941/25000000000000 : ℝ)^387
        have hw : |(1348618007/2500000000 : ℝ)|=(1348618007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s7_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312148701/10000000000 : ℝ)*x 0 + (269723611/500000000 : ℝ)*x 1 + (-268630479/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312148701/10000000000 : ℝ)^515 ≤ (43092682294593/100000000000000 : ℝ)^387 := by
    have hnat : (5312148701 : ℕ)^515*100000000000000^387 ≤ 43092682294593^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312148701 10000000000 43092682294593 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269723611/500000000 : ℝ)^515 ≤ (21991824307503/50000000000000 : ℝ)^387 := by
    have hnat : (269723611 : ℕ)^515*50000000000000^387 ≤ 21991824307503^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269723611 500000000 21991824307503 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268630479/1250000000 : ℝ)^515 ≤ (12923669079397/100000000000000 : ℝ)^387 := by
    have hnat : (268630479 : ℕ)^515*100000000000000^387 ≤ 12923669079397^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268630479 1250000000 12923669079397 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312148701/10000000000 : ℝ), (269723611/500000000 : ℝ), (-268630479/1250000000 : ℝ)] ![(43092682294593/100000000000000 : ℝ), (21991824307503/50000000000000 : ℝ), (12923669079397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312148701/10000000000 : ℝ)|^515 ≤ (43092682294593/100000000000000 : ℝ)^387
        have hw : |(5312148701/10000000000 : ℝ)|=(5312148701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269723611/500000000 : ℝ)|^515 ≤ (21991824307503/50000000000000 : ℝ)^387
        have hw : |(269723611/500000000 : ℝ)|=(269723611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268630479/1250000000 : ℝ)|^515 ≤ (12923669079397/100000000000000 : ℝ)^387
        have hw : |(-268630479/1250000000 : ℝ)|=(268630479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s7_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4378235841/10000000000 : ℝ)*x 0 + (2253592507/5000000000 : ℝ)*x 1 + (6804897/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378235841/10000000000 : ℝ)^515 ≤ (33316477514161/100000000000000 : ℝ)^387 := by
    have hnat : (4378235841 : ℕ)^515*100000000000000^387 ≤ 33316477514161^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378235841 10000000000 33316477514161 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253592507/5000000000 : ℝ)^515 ≤ (135267931911/390625000000 : ℝ)^387 := by
    have hnat : (2253592507 : ℕ)^515*390625000000^387 ≤ 135267931911^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253592507 5000000000 135267931911 390625000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6804897/16000000 : ℝ)^515 ≤ (32054931904777/100000000000000 : ℝ)^387 := by
    have hnat : (6804897 : ℕ)^515*100000000000000^387 ≤ 32054931904777^387*16000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6804897 16000000 32054931904777 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378235841/10000000000 : ℝ), (2253592507/5000000000 : ℝ), (6804897/16000000 : ℝ)] ![(33316477514161/100000000000000 : ℝ), (135267931911/390625000000 : ℝ), (32054931904777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378235841/10000000000 : ℝ)|^515 ≤ (33316477514161/100000000000000 : ℝ)^387
        have hw : |(4378235841/10000000000 : ℝ)|=(4378235841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253592507/5000000000 : ℝ)|^515 ≤ (135267931911/390625000000 : ℝ)^387
        have hw : |(2253592507/5000000000 : ℝ)|=(2253592507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6804897/16000000 : ℝ)|^515 ≤ (32054931904777/100000000000000 : ℝ)^387
        have hw : |(6804897/16000000 : ℝ)|=(6804897/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13993/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3501/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2803/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3501/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2803/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3501/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2803/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3501/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2803/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3501/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2803/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3501/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2803/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2803/25000 : ℝ) ^ (8239/2048 : ℝ) ≤ (15028766110932007/100000000000000000000 : ℝ) := by
    have hpowers : (2803/25000 : ℝ)^8239 ≤ (15028766110932007/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2803 : ℕ)^8239*100000000000000000000^2048 ≤ 15028766110932007^2048*25000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2803 25000 15028766110932007 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2803/25000 : ℝ)) (X := (15028766110932007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3501/25000 : ℝ) ^ (8239/2048 : ℝ) ≤ (9190847704982871/25000000000000000000 : ℝ) := by
    have hpowers : (3501/25000 : ℝ)^8239 ≤ (9190847704982871/25000000000000000000 : ℝ)^2048 := by
      have hnat : (3501 : ℕ)^8239*25000000000000000000^2048 ≤ 9190847704982871^2048*25000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3501 25000 9190847704982871 25000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3501/25000 : ℝ)) (X := (9190847704982871/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015028766110932007/50000000000000000000 : ℝ) ≤ (10000747067307683/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50015028766110932007/50000000000000000000 : ℝ)^2048 ≤ (10000747067307683/10000000000000000 : ℝ)^8239 := by
      have hnat : (50015028766110932007 : ℕ)^2048*10000000000000000^8239 ≤ 10000747067307683^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015028766110932007 50000000000000000000 10000747067307683 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000747067307683/10000000000000000 : ℝ)) (X := (50015028766110932007/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051792156930863491/100000000000000000000 : ℝ) ≤ (50006435835867/50000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (100051792156930863491/100000000000000000000 : ℝ)^2048 ≤ (50006435835867/50000000000000 : ℝ)^8239 := by
      have hnat : (100051792156930863491 : ℕ)^2048*50000000000000^8239 ≤ 50006435835867^8239*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051792156930863491 100000000000000000000 50006435835867 50000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50006435835867/50000000000000 : ℝ)) (X := (100051792156930863491/100000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509190847704982871/12500000000000000000 : ℝ) ≤ (10001827267039117/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (12509190847704982871/12500000000000000000 : ℝ)^2048 ≤ (10001827267039117/10000000000000000 : ℝ)^8239 := by
      have hnat : (12509190847704982871 : ℕ)^2048*10000000000000000^8239 ≤ 10001827267039117^8239*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509190847704982871 12500000000000000000 10001827267039117 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001827267039117/10000000000000000 : ℝ)) (X := (12509190847704982871/12500000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15028766110932007/100000000000000000000 : ℝ) ≤ ((436093353320847077/436250000000000000 : ℝ)+2*(540099865717/279200000000000 : ℝ)*(2803/25000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (436093353320847077/436250000000000000 : ℝ)+2*(540099865717/279200000000000 : ℝ)*(2803/25000 : ℝ)=(10000747067307683/10000000000000000 : ℝ) by norm_num, show 1+2*(15028766110932007/100000000000000000000 : ℝ)=(50015028766110932007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9190847704982871/25000000000000000000 : ℝ)+(15028766110932007/100000000000000000000 : ℝ) ≤ ((436093353320847077/436250000000000000 : ℝ)+(540099865717/279200000000000 : ℝ)*((3501/25000 : ℝ)+(2803/25000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (436093353320847077/436250000000000000 : ℝ)+(540099865717/279200000000000 : ℝ)*((3501/25000 : ℝ)+(2803/25000 : ℝ))=(50006435835867/50000000000000 : ℝ) by norm_num, show 1+(9190847704982871/25000000000000000000 : ℝ)+(15028766110932007/100000000000000000000 : ℝ)=(100051792156930863491/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9190847704982871/25000000000000000000 : ℝ) ≤ ((436093353320847077/436250000000000000 : ℝ)+2*(540099865717/279200000000000 : ℝ)*(3501/25000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (436093353320847077/436250000000000000 : ℝ)+2*(540099865717/279200000000000 : ℝ)*(3501/25000 : ℝ)=(10001827267039117/10000000000000000 : ℝ) by norm_num, show 1+2*(9190847704982871/25000000000000000000 : ℝ)=(12509190847704982871/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (436093353320847077/436250000000000000 : ℝ)*(X 1 0+X 2 0)+(540099865717/279200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (2803/25000 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (436093353320847077/436250000000000000 : ℝ)) (alpha := (540099865717/279200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (436093353320847077/436250000000000000 : ℝ)*(X 0 1+X 2 1)+(540099865717/279200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (2803/25000 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (436093353320847077/436250000000000000 : ℝ)) (alpha := (540099865717/279200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (436093353320847077/436250000000000000 : ℝ)*(X 0 2+X 1 2)+(540099865717/279200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (2803/25000 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (436093353320847077/436250000000000000 : ℝ)) (alpha := (540099865717/279200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1106575039/5000000000 : ℝ)*X 0 0+(1078960279/2000000000 : ℝ)*X 0 1+(82249831/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672523733/5000000000 : ℝ)*X 1 0+(-2279526987/10000000000 : ℝ)*X 1 1+(2631994581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345047469/10000000000 : ℝ)*X 2 0+(263199459/500000000 : ℝ)*X 2 1+(-2279526959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378226171/10000000000 : ℝ)*X 0 0+(4252417883/10000000000 : ℝ)*X 0 1+(4507825083/10000000000 : ℝ)*X 0 2+(4378226171/10000000000 : ℝ)*X 1 0+(4252417883/10000000000 : ℝ)*X 1 1+(4507825083/10000000000 : ℝ)*X 1 2+(4378226171/10000000000 : ℝ)*X 2 0+(4252417883/10000000000 : ℝ)*X 2 1+(4507825083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-88526211/400000000 : ℝ)*X 0 0+(5264317201/10000000000 : ℝ)*X 0 1+(5394472153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656074397/5000000000 : ℝ)*X 1 0+(-2149043967/10000000000 : ℝ)*X 1 1+(1348618007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312148701/10000000000 : ℝ)*X 2 0+(269723611/500000000 : ℝ)*X 2 1+(-268630479/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378235841/10000000000 : ℝ)*X 0 0+(2253592507/5000000000 : ℝ)*X 0 1+(6804897/16000000 : ℝ)*X 0 2+(4378235841/10000000000 : ℝ)*X 1 0+(2253592507/5000000000 : ℝ)*X 1 1+(6804897/16000000 : ℝ)*X 1 2+(4378235841/10000000000 : ℝ)*X 2 0+(2253592507/5000000000 : ℝ)*X 2 1+(6804897/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3949817508863869771193517/1363281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (54080853/10000000000000 : ℝ)*(base19) + (458790269/100000000000000 : ℝ)*(base23) + (23066261/50000000000000 : ℝ)*(lower2) + (34064939/50000000000000 : ℝ)*(upper3) + (1925027/4000000000000 : ℝ)*(upper5) + (180623494604891/3125000000000 : ℝ)*(major0) + (180623494604891/3125000000000 : ℝ)*(major1) + (180623494604891/3125000000000 : ℝ)*(major2) + (3822279468609463/50000000000000 : ℝ)*(sp0) + (59723214963523/781250000000 : ℝ)*(sp1) + (1911142899337301/25000000000000 : ℝ)*(sp2) + (156612939540463/4000000000000 : ℝ)*(sp3) + (13118920547/100000000000000 : ℝ)*(sp4) + (8013485723/100000000000000 : ℝ)*(sp7) + (1957665750998649/50000000000000 : ℝ)*(f.failure) + (3822286028069737/50000000000000 : ℝ)*(f.sum) + (2033197764713/1745000000000000000000000000 : ℝ)*base65 + (22424305039064661/2726562500000000000000000000000 : ℝ)*base68 + (38419567167801197/5453125000000000000000000000000 : ℝ)*base70 + (9136927272716589/2726562500000000000000000000000 : ℝ)*base71 + (455806054733/1745000000000000000000000000 : ℝ)*base73 + (9241756972158411/2726562500000000000000000000000 : ℝ)*base76 + (43025981230310339/2726562500000000000000000000000 : ℝ)*base77 + (6720261938238697/5453125000000000000000000000000 : ℝ)*base80 + (849436546237/109062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (11283869/2500000000000000000000 : ℝ)*base89 + (11283869/2500000000000000000000 : ℝ)*base91 + (11283869/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48502013233904679485817087/21812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224630809/50000000000000 : ℝ)*(base19) + (685055517/100000000000000 : ℝ)*(base23) + (285973/195312500000 : ℝ)*(upper2) + (5031667/50000000000000 : ℝ)*(lower5) + (2904558027345063/50000000000000 : ℝ)*(major0) + (2904558027345063/50000000000000 : ℝ)*(major1) + (2904558027345063/50000000000000 : ℝ)*(major2) + (1062106741/12500000000000 : ℝ)*(sp1) + (23226379/97656250000 : ℝ)*(sp2) + (788329047/20000000000000 : ℝ)*(sp3) + (120049136333699/1562500000000 : ℝ)*(sp4) + (7683135779241189/100000000000000 : ℝ)*(sp5) + (1920780064122281/25000000000000 : ℝ)*(sp6) + (245942710516167/6250000000000 : ℝ)*(sp7) + (3935087309903907/100000000000000 : ℝ)*(f.failure) + (120049136333699/1562500000000 : ℝ)*(f.sum) + (29752215864911/6980000000000000000000000000 : ℝ)*base65 + (529736401641103923/43625000000000000000000000000000 : ℝ)*base68 + (475506044783103923/43625000000000000000000000000000 : ℝ)*base70 + (106811852771646077/43625000000000000000000000000000 : ℝ)*base71 + (6790519751451/6980000000000000000000000000 : ℝ)*base73 + (469927149780603923/43625000000000000000000000000000 : ℝ)*base76 + (92274779911603923/43625000000000000000000000000000 : ℝ)*base78 + (986108023863103923/43625000000000000000000000000000 : ℝ)*base80 + (7834217799631/6980000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (14528367/5000000000000000000000 : ℝ)*base89 + (14528367/5000000000000000000000 : ℝ)*base91 + (14528367/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1047_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1047_s8_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213158793/10000000000 : ℝ)*x 0 + (5394682777/10000000000 : ℝ)*x 1 + (210564089/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213158793/10000000000 : ℝ)^515 ≤ (2687855415631/20000000000000 : ℝ)^387 := by
    have hnat : (2213158793 : ℕ)^515*20000000000000^387 ≤ 2687855415631^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213158793 10000000000 2687855415631 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394682777/10000000000 : ℝ)^515 ≤ (10996483304897/25000000000000 : ℝ)^387 := by
    have hnat : (5394682777 : ℕ)^515*25000000000000^387 ≤ 10996483304897^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394682777 10000000000 10996483304897 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210564089/400000000 : ℝ)^515 ≤ (42574789694531/100000000000000 : ℝ)^387 := by
    have hnat : (210564089 : ℕ)^515*100000000000000^387 ≤ 42574789694531^387*400000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210564089 400000000 42574789694531 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213158793/10000000000 : ℝ), (5394682777/10000000000 : ℝ), (210564089/400000000 : ℝ)] ![(2687855415631/20000000000000 : ℝ), (10996483304897/25000000000000 : ℝ), (42574789694531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213158793/10000000000 : ℝ)|^515 ≤ (2687855415631/20000000000000 : ℝ)^387
        have hw : |(-2213158793/10000000000 : ℝ)|=(2213158793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394682777/10000000000 : ℝ)|^515 ≤ (10996483304897/25000000000000 : ℝ)^387
        have hw : |(5394682777/10000000000 : ℝ)|=(5394682777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210564089/400000000 : ℝ)|^515 ≤ (42574789694531/100000000000000 : ℝ)^387
        have hw : |(210564089/400000000 : ℝ)|=(210564089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s8_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (6681273/12500000 : ℝ)*x 0 + (-2279416391/10000000000 : ℝ)*x 1 + (1316025557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6681273/12500000 : ℝ)^515 ≤ (21723939472441/50000000000000 : ℝ)^387 := by
    have hnat : (6681273 : ℕ)^515*50000000000000^387 ≤ 21723939472441^387*12500000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6681273 12500000 21723939472441 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279416391/10000000000 : ℝ)^515 ≤ (10919790087/78125000000 : ℝ)^387 := by
    have hnat : (2279416391 : ℕ)^515*78125000000^387 ≤ 10919790087^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279416391 10000000000 10919790087 78125000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316025557/2500000000 : ℝ)^515 ≤ (2128739486341/5000000000000 : ℝ)^387 := by
    have hnat : (1316025557 : ℕ)^515*5000000000000^387 ≤ 2128739486341^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316025557 2500000000 2128739486341 5000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6681273/12500000 : ℝ), (-2279416391/10000000000 : ℝ), (1316025557/2500000000 : ℝ)] ![(21723939472441/50000000000000 : ℝ), (10919790087/78125000000 : ℝ), (2128739486341/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6681273/12500000 : ℝ)|^515 ≤ (21723939472441/50000000000000 : ℝ)^387
        have hw : |(6681273/12500000 : ℝ)|=(6681273/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279416391/10000000000 : ℝ)|^515 ≤ (10919790087/78125000000 : ℝ)^387
        have hw : |(-2279416391/10000000000 : ℝ)|=(2279416391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316025557/2500000000 : ℝ)|^515 ≤ (2128739486341/5000000000000 : ℝ)^387
        have hw : |(1316025557/2500000000 : ℝ)|=(1316025557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s8_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668127301/1250000000 : ℝ)*x 0 + (329006389/625000000 : ℝ)*x 1 + (-2279416387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668127301/1250000000 : ℝ)^515 ≤ (43447879031419/100000000000000 : ℝ)^387 := by
    have hnat : (668127301 : ℕ)^515*100000000000000^387 ≤ 43447879031419^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668127301 1250000000 43447879031419 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329006389/625000000 : ℝ)^515 ≤ (42574789683769/100000000000000 : ℝ)^387 := by
    have hnat : (329006389 : ℕ)^515*100000000000000^387 ≤ 42574789683769^387*625000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329006389 625000000 42574789683769 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279416387/10000000000 : ℝ)^515 ≤ (13977331278719/100000000000000 : ℝ)^387 := by
    have hnat : (2279416387 : ℕ)^515*100000000000000^387 ≤ 13977331278719^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279416387 10000000000 13977331278719 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668127301/1250000000 : ℝ), (329006389/625000000 : ℝ), (-2279416387/10000000000 : ℝ)] ![(43447879031419/100000000000000 : ℝ), (42574789683769/100000000000000 : ℝ), (13977331278719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668127301/1250000000 : ℝ)|^515 ≤ (43447879031419/100000000000000 : ℝ)^387
        have hw : |(668127301/1250000000 : ℝ)|=(668127301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329006389/625000000 : ℝ)|^515 ≤ (42574789683769/100000000000000 : ℝ)^387
        have hw : |(329006389/625000000 : ℝ)|=(329006389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2279416387/10000000000 : ℝ)|^515 ≤ (13977331278719/100000000000000 : ℝ)^387
        have hw : |(-2279416387/10000000000 : ℝ)|=(2279416387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s8_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (547279009/1250000000 : ℝ)*x 0 + (2126321661/5000000000 : ℝ)*x 1 + (4507598103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547279009/1250000000 : ℝ)^515 ≤ (33316439347667/100000000000000 : ℝ)^387 := by
    have hnat : (547279009 : ℕ)^515*100000000000000^387 ≤ 33316439347667^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547279009 1250000000 33316439347667 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126321661/5000000000 : ℝ)^515 ≤ (32050746533313/100000000000000 : ℝ)^387 := by
    have hnat : (2126321661 : ℕ)^515*100000000000000^387 ≤ 32050746533313^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126321661 5000000000 32050746533313 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507598103/10000000000 : ℝ)^515 ≤ (865820352559/2500000000000 : ℝ)^387 := by
    have hnat : (4507598103 : ℕ)^515*2500000000000^387 ≤ 865820352559^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507598103 10000000000 865820352559 2500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547279009/1250000000 : ℝ), (2126321661/5000000000 : ℝ), (4507598103/10000000000 : ℝ)] ![(33316439347667/100000000000000 : ℝ), (32050746533313/100000000000000 : ℝ), (865820352559/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547279009/1250000000 : ℝ)|^515 ≤ (33316439347667/100000000000000 : ℝ)^387
        have hw : |(547279009/1250000000 : ℝ)|=(547279009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126321661/5000000000 : ℝ)|^515 ≤ (32050746533313/100000000000000 : ℝ)^387
        have hw : |(2126321661/5000000000 : ℝ)|=(2126321661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507598103/10000000000 : ℝ)|^515 ≤ (865820352559/2500000000000 : ℝ)^387
        have hw : |(4507598103/10000000000 : ℝ)|=(4507598103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s8_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-553290959/2500000000 : ℝ)*x 0 + (5264428841/10000000000 : ℝ)*x 1 + (2697177517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553290959/2500000000 : ℝ)^515 ≤ (1679914728767/12500000000000 : ℝ)^387 := by
    have hnat : (553290959 : ℕ)^515*12500000000000^387 ≤ 1679914728767^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553290959 2500000000 1679914728767 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264428841/10000000000 : ℝ)^515 ≤ (42578305026737/100000000000000 : ℝ)^387 := by
    have hnat : (5264428841 : ℕ)^515*100000000000000^387 ≤ 42578305026737^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264428841 10000000000 42578305026737 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697177517/5000000000 : ℝ)^515 ≤ (21991188562829/50000000000000 : ℝ)^387 := by
    have hnat : (2697177517 : ℕ)^515*50000000000000^387 ≤ 21991188562829^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697177517 5000000000 21991188562829 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553290959/2500000000 : ℝ), (5264428841/10000000000 : ℝ), (2697177517/5000000000 : ℝ)] ![(1679914728767/12500000000000 : ℝ), (42578305026737/100000000000000 : ℝ), (21991188562829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553290959/2500000000 : ℝ)|^515 ≤ (1679914728767/12500000000000 : ℝ)^387
        have hw : |(-553290959/2500000000 : ℝ)|=(553290959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264428841/10000000000 : ℝ)|^515 ≤ (42578305026737/100000000000000 : ℝ)^387
        have hw : |(5264428841/10000000000 : ℝ)|=(5264428841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697177517/5000000000 : ℝ)|^515 ≤ (21991188562829/50000000000000 : ℝ)^387
        have hw : |(2697177517/5000000000 : ℝ)|=(2697177517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s8_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (265608907/500000000 : ℝ)*x 0 + (-537290739/2500000000 : ℝ)*x 1 + (5394355067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265608907/500000000 : ℝ)^515 ≤ (21546500046977/50000000000000 : ℝ)^387 := by
    have hnat : (265608907 : ℕ)^515*50000000000000^387 ≤ 21546500046977^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265608907 500000000 21546500046977 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537290739/2500000000 : ℝ)^515 ≤ (1615577800299/12500000000000 : ℝ)^387 := by
    have hnat : (537290739 : ℕ)^515*12500000000000^387 ≤ 1615577800299^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537290739 2500000000 1615577800299 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394355067/10000000000 : ℝ)^515 ≤ (43982377483713/100000000000000 : ℝ)^387 := by
    have hnat : (5394355067 : ℕ)^515*100000000000000^387 ≤ 43982377483713^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394355067 10000000000 43982377483713 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265608907/500000000 : ℝ), (-537290739/2500000000 : ℝ), (5394355067/10000000000 : ℝ)] ![(21546500046977/50000000000000 : ℝ), (1615577800299/12500000000000 : ℝ), (43982377483713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265608907/500000000 : ℝ)|^515 ≤ (21546500046977/50000000000000 : ℝ)^387
        have hw : |(265608907/500000000 : ℝ)|=(265608907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537290739/2500000000 : ℝ)|^515 ≤ (1615577800299/12500000000000 : ℝ)^387
        have hw : |(-537290739/2500000000 : ℝ)|=(537290739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394355067/10000000000 : ℝ)|^515 ≤ (43982377483713/100000000000000 : ℝ)^387
        have hw : |(5394355067/10000000000 : ℝ)|=(5394355067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s8_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312176969/10000000000 : ℝ)*x 0 + (2697177441/5000000000 : ℝ)*x 1 + (-2149164787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312176969/10000000000 : ℝ)^515 ≤ (2693311715799/6250000000000 : ℝ)^387 := by
    have hnat : (5312176969 : ℕ)^515*6250000000000^387 ≤ 2693311715799^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312176969 10000000000 2693311715799 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697177441/5000000000 : ℝ)^515 ≤ (43982375476437/100000000000000 : ℝ)^387 := by
    have hnat : (2697177441 : ℕ)^515*100000000000000^387 ≤ 43982375476437^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697177441 5000000000 43982375476437 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149164787/10000000000 : ℝ)^515 ≤ (100973726997/781250000000 : ℝ)^387 := by
    have hnat : (2149164787 : ℕ)^515*781250000000^387 ≤ 100973726997^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149164787 10000000000 100973726997 781250000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312176969/10000000000 : ℝ), (2697177441/5000000000 : ℝ), (-2149164787/10000000000 : ℝ)] ![(2693311715799/6250000000000 : ℝ), (43982375476437/100000000000000 : ℝ), (100973726997/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312176969/10000000000 : ℝ)|^515 ≤ (2693311715799/6250000000000 : ℝ)^387
        have hw : |(5312176969/10000000000 : ℝ)|=(5312176969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697177441/5000000000 : ℝ)|^515 ≤ (43982375476437/100000000000000 : ℝ)^387
        have hw : |(2697177441/5000000000 : ℝ)|=(2697177441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149164787/10000000000 : ℝ)|^515 ≤ (100973726997/781250000000 : ℝ)^387
        have hw : |(-2149164787/10000000000 : ℝ)|=(2149164787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s8_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4378240821/10000000000 : ℝ)*x 0 + (4506960241/10000000000 : ℝ)*x 1 + (2126642361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378240821/10000000000 : ℝ)^515 ≤ (33316527943771/100000000000000 : ℝ)^387 := by
    have hnat : (4378240821 : ℕ)^515*100000000000000^387 ≤ 33316527943771^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378240821 10000000000 33316527943771 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506960241/10000000000 : ℝ)^515 ≤ (34626292483337/100000000000000 : ℝ)^387 := by
    have hnat : (4506960241 : ℕ)^515*100000000000000^387 ≤ 34626292483337^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506960241 10000000000 34626292483337 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126642361/5000000000 : ℝ)^515 ≤ (8014294889589/25000000000000 : ℝ)^387 := by
    have hnat : (2126642361 : ℕ)^515*25000000000000^387 ≤ 8014294889589^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126642361 5000000000 8014294889589 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378240821/10000000000 : ℝ), (4506960241/10000000000 : ℝ), (2126642361/5000000000 : ℝ)] ![(33316527943771/100000000000000 : ℝ), (34626292483337/100000000000000 : ℝ), (8014294889589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378240821/10000000000 : ℝ)|^515 ≤ (33316527943771/100000000000000 : ℝ)^387
        have hw : |(4378240821/10000000000 : ℝ)|=(4378240821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506960241/10000000000 : ℝ)|^515 ≤ (34626292483337/100000000000000 : ℝ)^387
        have hw : |(4506960241/10000000000 : ℝ)|=(4506960241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2126642361/5000000000 : ℝ)|^515 ≤ (8014294889589/25000000000000 : ℝ)^387
        have hw : |(2126642361/5000000000 : ℝ)|=(2126642361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (449/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13991/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11223/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (15088170896697377/100000000000000000000 : ℝ) := by
    have hpowers : (11223/100000 : ℝ)^8239 ≤ (15088170896697377/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11223 : ℕ)^8239*100000000000000000000^2048 ≤ 15088170896697377^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11223 100000 15088170896697377 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11223/100000 : ℝ)) (X := (15088170896697377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13993/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (7329471375595523/20000000000000000000 : ℝ) := by
    have hpowers : (13993/100000 : ℝ)^8239 ≤ (7329471375595523/20000000000000000000 : ℝ)^2048 := by
      have hnat : (13993 : ℕ)^8239*20000000000000000000^2048 ≤ 7329471375595523^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13993 100000 7329471375595523 20000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13993/100000 : ℝ)) (X := (7329471375595523/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015088170896697377/50000000000000000000 : ℝ) ≤ (5000375009967421/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50015088170896697377/50000000000000000000 : ℝ)^2048 ≤ (5000375009967421/5000000000000000 : ℝ)^8239 := by
      have hnat : (50015088170896697377 : ℕ)^2048*5000000000000000^8239 ≤ 5000375009967421^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015088170896697377 50000000000000000000 5000375009967421 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000375009967421/5000000000000000 : ℝ)) (X := (50015088170896697377/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253233470485917187/6250000000000000000 : ℝ) ≤ (1000128576006791/1000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (6253233470485917187/6250000000000000000 : ℝ)^2048 ≤ (1000128576006791/1000000000000000 : ℝ)^8239 := by
      have hnat : (6253233470485917187 : ℕ)^2048*1000000000000000^8239 ≤ 1000128576006791^8239*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253233470485917187 6250000000000000000 1000128576006791 1000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000128576006791/1000000000000000 : ℝ)) (X := (6253233470485917187/6250000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007329471375595523/10000000000000000000 : ℝ) ≤ (5000910750100489/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (10007329471375595523/10000000000000000000 : ℝ)^2048 ≤ (5000910750100489/5000000000000000 : ℝ)^8239 := by
      have hnat : (10007329471375595523 : ℕ)^2048*5000000000000000^8239 ≤ 5000910750100489^8239*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007329471375595523 10000000000000000000 5000910750100489 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000910750100489/5000000000000000 : ℝ)) (X := (10007329471375595523/10000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15088170896697377/100000000000000000000 : ℝ) ≤ ((6922513083048167003/6925000000000000000 : ℝ)+2*(133935033267/69250000000000 : ℝ)*(11223/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (6922513083048167003/6925000000000000000 : ℝ)+2*(133935033267/69250000000000 : ℝ)*(11223/100000 : ℝ)=(5000375009967421/5000000000000000 : ℝ) by norm_num, show 1+2*(15088170896697377/100000000000000000000 : ℝ)=(50015088170896697377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7329471375595523/20000000000000000000 : ℝ)+(15088170896697377/100000000000000000000 : ℝ) ≤ ((6922513083048167003/6925000000000000000 : ℝ)+(133935033267/69250000000000 : ℝ)*((13993/100000 : ℝ)+(11223/100000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (6922513083048167003/6925000000000000000 : ℝ)+(133935033267/69250000000000 : ℝ)*((13993/100000 : ℝ)+(11223/100000 : ℝ))=(1000128576006791/1000000000000000 : ℝ) by norm_num, show 1+(7329471375595523/20000000000000000000 : ℝ)+(15088170896697377/100000000000000000000 : ℝ)=(6253233470485917187/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7329471375595523/20000000000000000000 : ℝ) ≤ ((6922513083048167003/6925000000000000000 : ℝ)+2*(133935033267/69250000000000 : ℝ)*(13993/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (6922513083048167003/6925000000000000000 : ℝ)+2*(133935033267/69250000000000 : ℝ)*(13993/100000 : ℝ)=(5000910750100489/5000000000000000 : ℝ) by norm_num, show 1+2*(7329471375595523/20000000000000000000 : ℝ)=(10007329471375595523/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6922513083048167003/6925000000000000000 : ℝ)*(X 1 0+X 2 0)+(133935033267/69250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (6922513083048167003/6925000000000000000 : ℝ)) (alpha := (133935033267/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6922513083048167003/6925000000000000000 : ℝ)*(X 0 1+X 2 1)+(133935033267/69250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (6922513083048167003/6925000000000000000 : ℝ)) (alpha := (133935033267/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6922513083048167003/6925000000000000000 : ℝ)*(X 0 2+X 1 2)+(133935033267/69250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (6922513083048167003/6925000000000000000 : ℝ)) (alpha := (133935033267/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2213158793/10000000000 : ℝ)*X 0 0+(5394682777/10000000000 : ℝ)*X 0 1+(210564089/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((6681273/12500000 : ℝ)*X 1 0+(-2279416391/10000000000 : ℝ)*X 1 1+(1316025557/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668127301/1250000000 : ℝ)*X 2 0+(329006389/625000000 : ℝ)*X 2 1+(-2279416387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547279009/1250000000 : ℝ)*X 0 0+(2126321661/5000000000 : ℝ)*X 0 1+(4507598103/10000000000 : ℝ)*X 0 2+(547279009/1250000000 : ℝ)*X 1 0+(2126321661/5000000000 : ℝ)*X 1 1+(4507598103/10000000000 : ℝ)*X 1 2+(547279009/1250000000 : ℝ)*X 2 0+(2126321661/5000000000 : ℝ)*X 2 1+(4507598103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-553290959/2500000000 : ℝ)*X 0 0+(5264428841/10000000000 : ℝ)*X 0 1+(2697177517/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265608907/500000000 : ℝ)*X 1 0+(-537290739/2500000000 : ℝ)*X 1 1+(5394355067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312176969/10000000000 : ℝ)*X 2 0+(2697177441/5000000000 : ℝ)*X 2 1+(-2149164787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378240821/10000000000 : ℝ)*X 0 0+(4506960241/10000000000 : ℝ)*X 0 1+(2126642361/5000000000 : ℝ)*X 0 2+(4378240821/10000000000 : ℝ)*X 1 0+(4506960241/10000000000 : ℝ)*X 1 1+(2126642361/5000000000 : ℝ)*X 1 2+(4378240821/10000000000 : ℝ)*X 2 0+(4506960241/10000000000 : ℝ)*X 2 1+(2126642361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112851097855098500007396297/17312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1304290171/100000000000000 : ℝ)*(base19) + (1206539781/100000000000000 : ℝ)*(base23) + (11674861/20000000000000 : ℝ)*(lower2) + (83069767/50000000000000 : ℝ)*(upper3) + (47012457/50000000000000 : ℝ)*(upper5) + (289512015142967/5000000000000 : ℝ)*(major0) + (289512015142967/5000000000000 : ℝ)*(major1) + (289512015142967/5000000000000 : ℝ)*(major2) + (7658144642864173/100000000000000 : ℝ)*(sp0) + (7658178182844529/100000000000000 : ℝ)*(sp1) + (7658178280594919/100000000000000 : ℝ)*(sp2) + (490285180573873/12500000000000 : ℝ)*(sp3) + (34844270527/100000000000000 : ℝ)*(sp4) + (19456710491/100000000000000 : ℝ)*(sp7) + (1961150450650737/50000000000000 : ℝ)*(f.failure) + (76581794871347/1000000000000 : ℝ)*(f.sum) + (7221320901859/692500000000000000000000000 : ℝ)*base66 + (113945558963442901/34625000000000000000000000000000 : ℝ)*base67 + (35988240897192901/34625000000000000000000000000000 : ℝ)*base69 + (222710225824557099/34625000000000000000000000000000 : ℝ)*base72 + (3782751943847/346250000000000000000000000 : ℝ)*base74 + (48309797520567901/34625000000000000000000000000000 : ℝ)*base75 + (548252237387557099/34625000000000000000000000000000 : ℝ)*base78 + (4098361818942901/34625000000000000000000000000000 : ℝ)*base79 + (12434221452873/1385000000000000000000000000 : ℝ)*base82 + (6932597/2500000000000000000000 : ℝ)*base89 + (6932597/2500000000000000000000 : ℝ)*base91 + (6932597/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3795963962450325917310667683/346250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (292313291/50000000000000 : ℝ)*(base19) + (263443809/100000000000000 : ℝ)*(upper1) + (590370851/100000000000000 : ℝ)*(upper2) + (49807669/20000000000000 : ℝ)*(lower4) + (95063813/100000000000000 : ℝ)*(lower5) + (5819374373893729/100000000000000 : ℝ)*(major0) + (5819374373893729/100000000000000 : ℝ)*(major1) + (5819374373893729/100000000000000 : ℝ)*(major2) + (32879123177/100000000000000 : ℝ)*(sp0) + (37863321289/50000000000000 : ℝ)*(sp1) + (1539335844371297/20000000000000 : ℝ)*(sp4) + (7696635789710501/100000000000000 : ℝ)*(sp5) + (7696712100979661/100000000000000 : ℝ)*(sp6) + (985509070343007/25000000000000 : ℝ)*(sp7) + (985509070343007/25000000000000 : ℝ)*(f.failure) + (7696712100979661/100000000000000 : ℝ)*(f.sum) + (38804249316189/6925000000000000000000000000 : ℝ)*base66 + (6870444287054275813/692500000000000000000000000000000 : ℝ)*base68 + (4275283480086775813/692500000000000000000000000000000 : ℝ)*base70 + (1729319554509275813/692500000000000000000000000000000 : ℝ)*base72 + (6685203985459/1731250000000000000000000000 : ℝ)*base73 + (8819370170016775813/692500000000000000000000000000000 : ℝ)*base76 + (6942143891541775813/692500000000000000000000000000000 : ℝ)*base78 + (5677785184244275813/692500000000000000000000000000000 : ℝ)*base80 + (25513275772039/6925000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (15065467/1250000000000000000000 : ℝ)*base89 + (15065467/1250000000000000000000 : ℝ)*base91 + (15065467/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1047_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1047_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1047_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1047_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1047_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1047_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
