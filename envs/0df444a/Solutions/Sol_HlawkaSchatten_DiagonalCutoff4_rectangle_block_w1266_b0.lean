-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1266_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:48.713045+00:00
-- url     : https://prove2.me/submissions/fb5860e5-8a15-4a3e-a3dd-5a91ce65976f

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
theorem support_rectangle_w1266_s0_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1853177187/10000000000 : ℝ)*x 0 + (376632033/625000000 : ℝ)*x 1 + (2397975871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853177187/10000000000 : ℝ)^8459 ≤ (2703910618473/25000000000000 : ℝ)^6411 := by
    have hnat : (1853177187 : ℕ)^8459*25000000000000^6411 ≤ 2703910618473^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853177187 10000000000 2703910618473 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376632033/625000000 : ℝ)^8459 ≤ (12814743969441/25000000000000 : ℝ)^6411 := by
    have hnat : (376632033 : ℕ)^8459*25000000000000^6411 ≤ 12814743969441^6411*625000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376632033 625000000 12814743969441 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397975871/5000000000 : ℝ)^8459 ≤ (18962690813833/50000000000000 : ℝ)^6411 := by
    have hnat : (2397975871 : ℕ)^8459*50000000000000^6411 ≤ 18962690813833^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397975871 5000000000 18962690813833 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1853177187/10000000000 : ℝ), (376632033/625000000 : ℝ), (2397975871/5000000000 : ℝ)] ![(2703910618473/25000000000000 : ℝ), (12814743969441/25000000000000 : ℝ), (18962690813833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1853177187/10000000000 : ℝ)|^8459 ≤ (2703910618473/25000000000000 : ℝ)^6411
        have hw : |(-1853177187/10000000000 : ℝ)|=(1853177187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(376632033/625000000 : ℝ)|^8459 ≤ (12814743969441/25000000000000 : ℝ)^6411
        have hw : |(376632033/625000000 : ℝ)|=(376632033/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397975871/5000000000 : ℝ)|^8459 ≤ (18962690813833/50000000000000 : ℝ)^6411
        have hw : |(2397975871/5000000000 : ℝ)|=(2397975871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s0_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5509807413/10000000000 : ℝ)*x 0 + (-638947707/2500000000 : ℝ)*x 1 + (4795951717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509807413/10000000000 : ℝ)^8459 ≤ (22772578515309/50000000000000 : ℝ)^6411 := by
    have hnat : (5509807413 : ℕ)^8459*50000000000000^6411 ≤ 22772578515309^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509807413 10000000000 22772578515309 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (638947707/2500000000 : ℝ)^8459 ≤ (16529461586123/100000000000000 : ℝ)^6411 := by
    have hnat : (638947707 : ℕ)^8459*100000000000000^6411 ≤ 16529461586123^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638947707 2500000000 16529461586123 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795951717/10000000000 : ℝ)^8459 ≤ (37925381366817/100000000000000 : ℝ)^6411 := by
    have hnat : (4795951717 : ℕ)^8459*100000000000000^6411 ≤ 37925381366817^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795951717 10000000000 37925381366817 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509807413/10000000000 : ℝ), (-638947707/2500000000 : ℝ), (4795951717/10000000000 : ℝ)] ![(22772578515309/50000000000000 : ℝ), (16529461586123/100000000000000 : ℝ), (37925381366817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509807413/10000000000 : ℝ)|^8459 ≤ (22772578515309/50000000000000 : ℝ)^6411
        have hw : |(5509807413/10000000000 : ℝ)|=(5509807413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-638947707/2500000000 : ℝ)|^8459 ≤ (16529461586123/100000000000000 : ℝ)^6411
        have hw : |(-638947707/2500000000 : ℝ)|=(638947707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795951717/10000000000 : ℝ)|^8459 ≤ (37925381366817/100000000000000 : ℝ)^6411
        have hw : |(4795951717/10000000000 : ℝ)|=(4795951717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s0_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1377451859/2500000000 : ℝ)*x 0 + (959190343/2000000000 : ℝ)*x 1 + (-6389477/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377451859/2500000000 : ℝ)^8459 ≤ (11386289320369/25000000000000 : ℝ)^6411 := by
    have hnat : (1377451859 : ℕ)^8459*25000000000000^6411 ≤ 11386289320369^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377451859 2500000000 11386289320369 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959190343/2000000000 : ℝ)^8459 ≤ (37925381345949/100000000000000 : ℝ)^6411 := by
    have hnat : (959190343 : ℕ)^8459*100000000000000^6411 ≤ 37925381345949^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959190343 2000000000 37925381345949 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6389477/25000000 : ℝ)^8459 ≤ (8264730673593/50000000000000 : ℝ)^6411 := by
    have hnat : (6389477 : ℕ)^8459*50000000000000^6411 ≤ 8264730673593^6411*25000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6389477 25000000 8264730673593 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377451859/2500000000 : ℝ), (959190343/2000000000 : ℝ), (-6389477/25000000 : ℝ)] ![(11386289320369/25000000000000 : ℝ), (37925381345949/100000000000000 : ℝ), (8264730673593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377451859/2500000000 : ℝ)|^8459 ≤ (11386289320369/25000000000000 : ℝ)^6411
        have hw : |(1377451859/2500000000 : ℝ)|=(1377451859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(959190343/2000000000 : ℝ)|^8459 ≤ (37925381345949/100000000000000 : ℝ)^6411
        have hw : |(959190343/2000000000 : ℝ)|=(959190343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6389477/25000000 : ℝ)|^8459 ≤ (8264730673593/50000000000000 : ℝ)^6411
        have hw : |(-6389477/25000000 : ℝ)|=(6389477/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s0_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (65486609/156250000 : ℝ)*x 0 + (623202963/2000000000 : ℝ)*x 1 + (702881501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65486609/156250000 : ℝ)^8459 ≤ (31745796631793/100000000000000 : ℝ)^6411 := by
    have hnat : (65486609 : ℕ)^8459*100000000000000^6411 ≤ 31745796631793^6411*156250000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65486609 156250000 31745796631793 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623202963/2000000000 : ℝ)^8459 ≤ (10734934650633/50000000000000 : ℝ)^6411 := by
    have hnat : (623202963 : ℕ)^8459*50000000000000^6411 ≤ 10734934650633^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623202963 2000000000 10734934650633 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702881501/1250000000 : ℝ)^8459 ≤ (2339216702221/5000000000000 : ℝ)^6411 := by
    have hnat : (702881501 : ℕ)^8459*5000000000000^6411 ≤ 2339216702221^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702881501 1250000000 2339216702221 5000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65486609/156250000 : ℝ), (623202963/2000000000 : ℝ), (702881501/1250000000 : ℝ)] ![(31745796631793/100000000000000 : ℝ), (10734934650633/50000000000000 : ℝ), (2339216702221/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65486609/156250000 : ℝ)|^8459 ≤ (31745796631793/100000000000000 : ℝ)^6411
        have hw : |(65486609/156250000 : ℝ)|=(65486609/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623202963/2000000000 : ℝ)|^8459 ≤ (10734934650633/50000000000000 : ℝ)^6411
        have hw : |(623202963/2000000000 : ℝ)|=(623202963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(702881501/1250000000 : ℝ)|^8459 ≤ (2339216702221/5000000000000 : ℝ)^6411
        have hw : |(702881501/1250000000 : ℝ)|=(702881501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s0_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-4644917/25000000 : ℝ)*x 0 + (60345187/125000000 : ℝ)*x 1 + (2996664737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4644917/25000000 : ℝ)^8459 ≤ (1085254092971/10000000000000 : ℝ)^6411 := by
    have hnat : (4644917 : ℕ)^8459*10000000000000^6411 ≤ 1085254092971^6411*25000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4644917 25000000 1085254092971 10000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60345187/125000000 : ℝ)^8459 ≤ (2391006353737/6250000000000 : ℝ)^6411 := by
    have hnat : (60345187 : ℕ)^8459*6250000000000^6411 ≤ 2391006353737^6411*125000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60345187 125000000 2391006353737 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2996664737/5000000000 : ℝ)^8459 ≤ (50891357392809/100000000000000 : ℝ)^6411 := by
    have hnat : (2996664737 : ℕ)^8459*100000000000000^6411 ≤ 50891357392809^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996664737 5000000000 50891357392809 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4644917/25000000 : ℝ), (60345187/125000000 : ℝ), (2996664737/5000000000 : ℝ)] ![(1085254092971/10000000000000 : ℝ), (2391006353737/6250000000000 : ℝ), (50891357392809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4644917/25000000 : ℝ)|^8459 ≤ (1085254092971/10000000000000 : ℝ)^6411
        have hw : |(-4644917/25000000 : ℝ)|=(4644917/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60345187/125000000 : ℝ)|^8459 ≤ (2391006353737/6250000000000 : ℝ)^6411
        have hw : |(60345187/125000000 : ℝ)|=(60345187/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2996664737/5000000000 : ℝ)|^8459 ≤ (50891357392809/100000000000000 : ℝ)^6411
        have hw : |(2996664737/5000000000 : ℝ)|=(2996664737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s0_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174999009/10000000000 : ℝ)*x 0 + (-1358410637/10000000000 : ℝ)*x 1 + (2996665961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174999009/10000000000 : ℝ)^8459 ≤ (1310293717557/3125000000000 : ℝ)^6411 := by
    have hnat : (5174999009 : ℕ)^8459*3125000000000^6411 ≤ 1310293717557^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174999009 10000000000 1310293717557 3125000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358410637/10000000000 : ℝ)^8459 ≤ (3589608098257/50000000000000 : ℝ)^6411 := by
    have hnat : (1358410637 : ℕ)^8459*50000000000000^6411 ≤ 3589608098257^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358410637 10000000000 3589608098257 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2996665961/5000000000 : ℝ)^8459 ≤ (3180711551247/6250000000000 : ℝ)^6411 := by
    have hnat : (2996665961 : ℕ)^8459*6250000000000^6411 ≤ 3180711551247^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996665961 5000000000 3180711551247 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174999009/10000000000 : ℝ), (-1358410637/10000000000 : ℝ), (2996665961/5000000000 : ℝ)] ![(1310293717557/3125000000000 : ℝ), (3589608098257/50000000000000 : ℝ), (3180711551247/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174999009/10000000000 : ℝ)|^8459 ≤ (1310293717557/3125000000000 : ℝ)^6411
        have hw : |(5174999009/10000000000 : ℝ)|=(5174999009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358410637/10000000000 : ℝ)|^8459 ≤ (3589608098257/50000000000000 : ℝ)^6411
        have hw : |(-1358410637/10000000000 : ℝ)|=(1358410637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2996665961/5000000000 : ℝ)|^8459 ≤ (3180711551247/6250000000000 : ℝ)^6411
        have hw : |(2996665961/5000000000 : ℝ)|=(2996665961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s0_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5175000099/10000000000 : ℝ)*x 0 + (187291559/312500000 : ℝ)*x 1 + (-271682447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175000099/10000000000 : ℝ)^8459 ≤ (20964705307283/50000000000000 : ℝ)^6411 := by
    have hnat : (5175000099 : ℕ)^8459*50000000000000^6411 ≤ 20964705307283^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175000099 10000000000 20964705307283 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187291559/312500000 : ℝ)^8459 ≤ (50891362031223/100000000000000 : ℝ)^6411 := by
    have hnat : (187291559 : ℕ)^8459*100000000000000^6411 ≤ 50891362031223^6411*312500000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187291559 312500000 50891362031223 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271682447/2000000000 : ℝ)^8459 ≤ (224350854371/3125000000000 : ℝ)^6411 := by
    have hnat : (271682447 : ℕ)^8459*3125000000000^6411 ≤ 224350854371^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271682447 2000000000 224350854371 3125000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175000099/10000000000 : ℝ), (187291559/312500000 : ℝ), (-271682447/2000000000 : ℝ)] ![(20964705307283/50000000000000 : ℝ), (50891362031223/100000000000000 : ℝ), (224350854371/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175000099/10000000000 : ℝ)|^8459 ≤ (20964705307283/50000000000000 : ℝ)^6411
        have hw : |(5175000099/10000000000 : ℝ)|=(5175000099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(187291559/312500000 : ℝ)|^8459 ≤ (50891362031223/100000000000000 : ℝ)^6411
        have hw : |(187291559/312500000 : ℝ)|=(187291559/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271682447/2000000000 : ℝ)|^8459 ≤ (224350854371/3125000000000 : ℝ)^6411
        have hw : |(-271682447/2000000000 : ℝ)|=(271682447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s0_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (525113359/1250000000 : ℝ)*x 0 + (2779264579/5000000000 : ℝ)*x 1 + (79570493/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525113359/1250000000 : ℝ)^8459 ≤ (15921707510121/50000000000000 : ℝ)^6411 := by
    have hnat : (525113359 : ℕ)^8459*50000000000000^6411 ≤ 15921707510121^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525113359 1250000000 15921707510121 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779264579/5000000000 : ℝ)^8459 ≤ (2879831654601/6250000000000 : ℝ)^6411 := by
    have hnat : (2779264579 : ℕ)^8459*6250000000000^6411 ≤ 2879831654601^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779264579 5000000000 2879831654601 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79570493/250000000 : ℝ)^8459 ≤ (22079278483913/100000000000000 : ℝ)^6411 := by
    have hnat : (79570493 : ℕ)^8459*100000000000000^6411 ≤ 22079278483913^6411*250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79570493 250000000 22079278483913 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525113359/1250000000 : ℝ), (2779264579/5000000000 : ℝ), (79570493/250000000 : ℝ)] ![(15921707510121/50000000000000 : ℝ), (2879831654601/6250000000000 : ℝ), (22079278483913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525113359/1250000000 : ℝ)|^8459 ≤ (15921707510121/50000000000000 : ℝ)^6411
        have hw : |(525113359/1250000000 : ℝ)|=(525113359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2779264579/5000000000 : ℝ)|^8459 ≤ (2879831654601/6250000000000 : ℝ)^6411
        have hw : |(2779264579/5000000000 : ℝ)|=(2779264579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79570493/250000000 : ℝ)|^8459 ≤ (22079278483913/100000000000000 : ℝ)^6411
        have hw : |(79570493/250000000 : ℝ)|=(79570493/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (913/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27347/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4229/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4229 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4229*1^1024 ≤ 0^1024*1^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4229/1024 : ℝ) ≤ (71023884178324597/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4229 ≤ (71023884178324597/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4229*3125000000000000000^1024 ≤ 71023884178324597^1024*5^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 71023884178324597 3125000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (71023884178324597/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4229 := by
      have hnat : (1 : ℕ)^1024*1^4229 ≤ 1^4229*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3196023884178324597/3125000000000000000 : ℝ) ≤ (10054564439668141/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (3196023884178324597/3125000000000000000 : ℝ)^1024 ≤ (10054564439668141/10000000000000000 : ℝ)^4229 := by
      have hnat : (3196023884178324597 : ℕ)^1024*10000000000000000^4229 ≤ 10054564439668141^4229*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3196023884178324597 3125000000000000000 10054564439668141 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054564439668141/10000000000000000 : ℝ)) (X := (3196023884178324597/3125000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1633523884178324597/1562500000000000000 : ℝ) ≤ (5054564439668141/5000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (1633523884178324597/1562500000000000000 : ℝ)^1024 ≤ (5054564439668141/5000000000000000 : ℝ)^4229 := by
      have hnat : (1633523884178324597 : ℕ)^1024*5000000000000000^4229 ≤ 5054564439668141^4229*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1633523884178324597 1562500000000000000 5054564439668141 5000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054564439668141/5000000000000000 : ℝ)) (X := (1633523884178324597/1562500000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54564439668141/4000000000000000 : ℝ)*(0 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(54564439668141/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71023884178324597/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54564439668141/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (1 : ℝ)+(54564439668141/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054564439668141/10000000000000000 : ℝ) by norm_num, show 1+(71023884178324597/3125000000000000000 : ℝ)+(0 : ℝ)=(3196023884178324597/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71023884178324597/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54564439668141/4000000000000000 : ℝ)*(2/5 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(54564439668141/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054564439668141/5000000000000000 : ℝ) by norm_num, show 1+2*(71023884178324597/3125000000000000000 : ℝ)=(1633523884178324597/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54564439668141/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54564439668141/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54564439668141/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54564439668141/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54564439668141/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54564439668141/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1853177187/10000000000 : ℝ)*X 0 0+(376632033/625000000 : ℝ)*X 0 1+(2397975871/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5509807413/10000000000 : ℝ)*X 1 0+(-638947707/2500000000 : ℝ)*X 1 1+(4795951717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1377451859/2500000000 : ℝ)*X 2 0+(959190343/2000000000 : ℝ)*X 2 1+(-6389477/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((65486609/156250000 : ℝ)*X 0 0+(623202963/2000000000 : ℝ)*X 0 1+(702881501/1250000000 : ℝ)*X 0 2+(65486609/156250000 : ℝ)*X 1 0+(623202963/2000000000 : ℝ)*X 1 1+(702881501/1250000000 : ℝ)*X 1 2+(65486609/156250000 : ℝ)*X 2 0+(623202963/2000000000 : ℝ)*X 2 1+(702881501/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4644917/25000000 : ℝ)*X 0 0+(60345187/125000000 : ℝ)*X 0 1+(2996664737/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174999009/10000000000 : ℝ)*X 1 0+(-1358410637/10000000000 : ℝ)*X 1 1+(2996665961/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175000099/10000000000 : ℝ)*X 2 0+(187291559/312500000 : ℝ)*X 2 1+(-271682447/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((525113359/1250000000 : ℝ)*X 0 0+(2779264579/5000000000 : ℝ)*X 0 1+(79570493/250000000 : ℝ)*X 0 2+(525113359/1250000000 : ℝ)*X 1 0+(2779264579/5000000000 : ℝ)*X 1 1+(79570493/250000000 : ℝ)*X 1 2+(525113359/1250000000 : ℝ)*X 2 0+(2779264579/5000000000 : ℝ)*X 2 1+(79570493/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112476438048494356272267/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31762099/50000000000000 : ℝ)*(base1) + (684233661/50000000000000 : ℝ)*(base19) + (342965177/25000000000000 : ℝ)*(base23) + (31146731/20000000000000 : ℝ)*(upper3) + (163644949/100000000000000 : ℝ)*(upper5) + (302947968068029/50000000000000 : ℝ)*(major0) + (302947968068029/50000000000000 : ℝ)*(major1) + (302947968068029/50000000000000 : ℝ)*(major2) + (50806622648807/6250000000000 : ℝ)*(sp0) + (812908905994173/100000000000000 : ℝ)*(sp1) + (812908902600787/100000000000000 : ℝ)*(sp2) + (99719808089641/25000000000000 : ℝ)*(sp3) + (4375604781/100000000000000 : ℝ)*(sp4) + (528616781/25000000000000 : ℝ)*(sp7) + (199440705174943/50000000000000 : ℝ)*(f.failure) + (162582054892299/20000000000000 : ℝ)*(f.sum) + (116426052835911/100000000000000000000000000000 : ℝ)*base66 + (1228829637635911/200000000000000000000000000000 : ℝ)*base68 + (1595775466035911/200000000000000000000000000000 : ℝ)*base70 + (881831736235911/200000000000000000000000000000 : ℝ)*base72 + (488214528835911/100000000000000000000000000000 : ℝ)*base74 + (330731694635911/200000000000000000000000000000 : ℝ)*base76 + (1166201272835911/200000000000000000000000000000 : ℝ)*base78 + (359448280564089/200000000000000000000000000000 : ℝ)*base79 + (520218547235911/100000000000000000000000000000 : ℝ)*base82 + (10129079/1000000000000000000000 : ℝ)*base89 + (10129079/1000000000000000000000 : ℝ)*base91 + (10129079/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (863332999288038691156611/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288014087/100000000000000 : ℝ)*(base1) + (1923574649/100000000000000 : ℝ)*(base19) + (209586853/10000000000000 : ℝ)*(base23) + (74615559/20000000000000 : ℝ)*(upper3) + (7453023/12500000000000 : ℝ)*(upper5) + (319692285491557/50000000000000 : ℝ)*(major0) + (319692285491557/50000000000000 : ℝ)*(major1) + (319692285491557/50000000000000 : ℝ)*(major2) + (90827/2500000000 : ℝ)*(sp1) + (875848663/25000000000000 : ℝ)*(sp2) + (5490182731/640000000 : ℝ)*(sp4) + (428917603525007/50000000000000 : ℝ)*(sp5) + (428917582220741/50000000000000 : ℝ)*(sp6) + (84185560493961/20000000000000 : ℝ)*(sp7) + (105232022620973/25000000000000 : ℝ)*(f.failure) + (107230095463083/12500000000000 : ℝ)*(f.sum) + (25687858614463/100000000000000000000000000000 : ℝ)*base66 + (826347299385537/200000000000000000000000000000 : ℝ)*base67 + (1188136282614463/200000000000000000000000000000 : ℝ)*base70 + (33766920185537/200000000000000000000000000000 : ℝ)*base71 + (399438610185537/100000000000000000000000000000 : ℝ)*base73 + (887529835785537/200000000000000000000000000000 : ℝ)*base75 + (1401525652614463/200000000000000000000000000000 : ℝ)*base78 + (626921139814463/200000000000000000000000000000 : ℝ)*base80 + (191479935614463/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2359669/500000000000000000000 : ℝ)*base89 + (2359669/500000000000000000000 : ℝ)*base91 + (2359669/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1266_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27347/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1266_s1_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-409767447/2000000000 : ℝ)*x 0 + (5669640771/10000000000 : ℝ)*x 1 + (5027177591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409767447/2000000000 : ℝ)^8459 ≤ (12347182464017/100000000000000 : ℝ)^6411 := by
    have hnat : (409767447 : ℕ)^8459*100000000000000^6411 ≤ 12347182464017^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409767447 2000000000 12347182464017 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5669640771/10000000000 : ℝ)^8459 ≤ (11824114785263/25000000000000 : ℝ)^6411 := by
    have hnat : (5669640771 : ℕ)^8459*25000000000000^6411 ≤ 11824114785263^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669640771 10000000000 11824114785263 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027177591/10000000000 : ℝ)^8459 ≤ (10089089594783/25000000000000 : ℝ)^6411 := by
    have hnat : (5027177591 : ℕ)^8459*25000000000000^6411 ≤ 10089089594783^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027177591 10000000000 10089089594783 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409767447/2000000000 : ℝ), (5669640771/10000000000 : ℝ), (5027177591/10000000000 : ℝ)] ![(12347182464017/100000000000000 : ℝ), (11824114785263/25000000000000 : ℝ), (10089089594783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409767447/2000000000 : ℝ)|^8459 ≤ (12347182464017/100000000000000 : ℝ)^6411
        have hw : |(-409767447/2000000000 : ℝ)|=(409767447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5669640771/10000000000 : ℝ)|^8459 ≤ (11824114785263/25000000000000 : ℝ)^6411
        have hw : |(5669640771/10000000000 : ℝ)|=(5669640771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027177591/10000000000 : ℝ)|^8459 ≤ (10089089594783/25000000000000 : ℝ)^6411
        have hw : |(5027177591/10000000000 : ℝ)|=(5027177591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s1_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541236009/1000000000 : ℝ)*x 0 + (-2393440319/10000000000 : ℝ)*x 1 + (157099307/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541236009/1000000000 : ℝ)^8459 ≤ (44485329040739/100000000000000 : ℝ)^6411 := by
    have hnat : (541236009 : ℕ)^8459*100000000000000^6411 ≤ 44485329040739^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541236009 1000000000 44485329040739 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2393440319/10000000000 : ℝ)^8459 ≤ (3789577523057/25000000000000 : ℝ)^6411 := by
    have hnat : (2393440319 : ℕ)^8459*25000000000000^6411 ≤ 3789577523057^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393440319 10000000000 3789577523057 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157099307/312500000 : ℝ)^8459 ≤ (8071272169417/20000000000000 : ℝ)^6411 := by
    have hnat : (157099307 : ℕ)^8459*20000000000000^6411 ≤ 8071272169417^6411*312500000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157099307 312500000 8071272169417 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541236009/1000000000 : ℝ), (-2393440319/10000000000 : ℝ), (157099307/312500000 : ℝ)] ![(44485329040739/100000000000000 : ℝ), (3789577523057/25000000000000 : ℝ), (8071272169417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541236009/1000000000 : ℝ)|^8459 ≤ (44485329040739/100000000000000 : ℝ)^6411
        have hw : |(541236009/1000000000 : ℝ)|=(541236009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2393440319/10000000000 : ℝ)|^8459 ≤ (3789577523057/25000000000000 : ℝ)^6411
        have hw : |(-2393440319/10000000000 : ℝ)|=(2393440319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157099307/312500000 : ℝ)|^8459 ≤ (8071272169417/20000000000000 : ℝ)^6411
        have hw : |(157099307/312500000 : ℝ)|=(157099307/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s1_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5412360301/10000000000 : ℝ)*x 0 + (157099303/312500000 : ℝ)*x 1 + (-2393440207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412360301/10000000000 : ℝ)^8459 ≤ (44485331329001/100000000000000 : ℝ)^6411 := by
    have hnat : (5412360301 : ℕ)^8459*100000000000000^6411 ≤ 44485331329001^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412360301 10000000000 44485331329001 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157099303/312500000 : ℝ)^8459 ≤ (403563594913/1000000000000 : ℝ)^6411 := by
    have hnat : (157099303 : ℕ)^8459*1000000000000^6411 ≤ 403563594913^6411*312500000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157099303 312500000 403563594913 1000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2393440207/10000000000 : ℝ)^8459 ≤ (7579154578153/50000000000000 : ℝ)^6411 := by
    have hnat : (2393440207 : ℕ)^8459*50000000000000^6411 ≤ 7579154578153^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393440207 10000000000 7579154578153 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412360301/10000000000 : ℝ), (157099303/312500000 : ℝ), (-2393440207/10000000000 : ℝ)] ![(44485331329001/100000000000000 : ℝ), (403563594913/1000000000000 : ℝ), (7579154578153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412360301/10000000000 : ℝ)|^8459 ≤ (44485331329001/100000000000000 : ℝ)^6411
        have hw : |(5412360301/10000000000 : ℝ)|=(5412360301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(157099303/312500000 : ℝ)|^8459 ≤ (403563594913/1000000000000 : ℝ)^6411
        have hw : |(157099303/312500000 : ℝ)|=(157099303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2393440207/10000000000 : ℝ)|^8459 ≤ (7579154578153/50000000000000 : ℝ)^6411
        have hw : |(-2393440207/10000000000 : ℝ)|=(2393440207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s1_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2153381497/5000000000 : ℝ)*x 0 + (739946251/2000000000 : ℝ)*x 1 + (5009055919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153381497/5000000000 : ℝ)^8459 ≤ (16453191784273/50000000000000 : ℝ)^6411 := by
    have hnat : (2153381497 : ℕ)^8459*50000000000000^6411 ≤ 16453191784273^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153381497 5000000000 16453191784273 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739946251/2000000000 : ℝ)^8459 ≤ (5385818702963/20000000000000 : ℝ)^6411 := by
    have hnat : (739946251 : ℕ)^8459*20000000000000^6411 ≤ 5385818702963^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739946251 2000000000 5385818702963 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5009055919/10000000000 : ℝ)^8459 ≤ (40164522902281/100000000000000 : ℝ)^6411 := by
    have hnat : (5009055919 : ℕ)^8459*100000000000000^6411 ≤ 40164522902281^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009055919 10000000000 40164522902281 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153381497/5000000000 : ℝ), (739946251/2000000000 : ℝ), (5009055919/10000000000 : ℝ)] ![(16453191784273/50000000000000 : ℝ), (5385818702963/20000000000000 : ℝ), (40164522902281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153381497/5000000000 : ℝ)|^8459 ≤ (16453191784273/50000000000000 : ℝ)^6411
        have hw : |(2153381497/5000000000 : ℝ)|=(2153381497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(739946251/2000000000 : ℝ)|^8459 ≤ (5385818702963/20000000000000 : ℝ)^6411
        have hw : |(739946251/2000000000 : ℝ)|=(739946251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5009055919/10000000000 : ℝ)|^8459 ≤ (40164522902281/100000000000000 : ℝ)^6411
        have hw : |(5009055919/10000000000 : ℝ)|=(5009055919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s1_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-512371417/2500000000 : ℝ)*x 0 + (5035538101/10000000000 : ℝ)*x 1 + (1415280683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512371417/2500000000 : ℝ)^8459 ≤ (1544042349271/12500000000000 : ℝ)^6411 := by
    have hnat : (512371417 : ℕ)^8459*12500000000000^6411 ≤ 1544042349271^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512371417 2500000000 1544042349271 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5035538101/10000000000 : ℝ)^8459 ≤ (40444937030893/100000000000000 : ℝ)^6411 := by
    have hnat : (5035538101 : ℕ)^8459*100000000000000^6411 ≤ 40444937030893^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035538101 10000000000 40444937030893 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1415280683/2500000000 : ℝ)^8459 ≤ (47202724160889/100000000000000 : ℝ)^6411 := by
    have hnat : (1415280683 : ℕ)^8459*100000000000000^6411 ≤ 47202724160889^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415280683 2500000000 47202724160889 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-512371417/2500000000 : ℝ), (5035538101/10000000000 : ℝ), (1415280683/2500000000 : ℝ)] ![(1544042349271/12500000000000 : ℝ), (40444937030893/100000000000000 : ℝ), (47202724160889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-512371417/2500000000 : ℝ)|^8459 ≤ (1544042349271/12500000000000 : ℝ)^6411
        have hw : |(-512371417/2500000000 : ℝ)|=(512371417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5035538101/10000000000 : ℝ)|^8459 ≤ (40444937030893/100000000000000 : ℝ)^6411
        have hw : |(5035538101/10000000000 : ℝ)|=(5035538101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1415280683/2500000000 : ℝ)|^8459 ≤ (47202724160889/100000000000000 : ℝ)^6411
        have hw : |(1415280683/2500000000 : ℝ)|=(1415280683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s1_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327916041/625000000 : ℝ)*x 0 + (-1759494999/10000000000 : ℝ)*x 1 + (1415280807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327916041/625000000 : ℝ)^8459 ≤ (21348575195239/50000000000000 : ℝ)^6411 := by
    have hnat : (327916041 : ℕ)^8459*50000000000000^6411 ≤ 21348575195239^6411*625000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327916041 625000000 21348575195239 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1759494999/10000000000 : ℝ)^8459 ≤ (5050059992139/50000000000000 : ℝ)^6411 := by
    have hnat : (1759494999 : ℕ)^8459*50000000000000^6411 ≤ 5050059992139^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759494999 10000000000 5050059992139 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1415280807/2500000000 : ℝ)^8459 ≤ (47202729617707/100000000000000 : ℝ)^6411 := by
    have hnat : (1415280807 : ℕ)^8459*100000000000000^6411 ≤ 47202729617707^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415280807 2500000000 47202729617707 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327916041/625000000 : ℝ), (-1759494999/10000000000 : ℝ), (1415280807/2500000000 : ℝ)] ![(21348575195239/50000000000000 : ℝ), (5050059992139/50000000000000 : ℝ), (47202729617707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327916041/625000000 : ℝ)|^8459 ≤ (21348575195239/50000000000000 : ℝ)^6411
        have hw : |(327916041/625000000 : ℝ)|=(327916041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1759494999/10000000000 : ℝ)|^8459 ≤ (5050059992139/50000000000000 : ℝ)^6411
        have hw : |(-1759494999/10000000000 : ℝ)|=(1759494999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1415280807/2500000000 : ℝ)|^8459 ≤ (47202729617707/100000000000000 : ℝ)^6411
        have hw : |(1415280807/2500000000 : ℝ)|=(1415280807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s1_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1311664143/2500000000 : ℝ)*x 0 + (141528073/250000000 : ℝ)*x 1 + (-439873891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311664143/2500000000 : ℝ)^8459 ≤ (8539429897703/20000000000000 : ℝ)^6411 := by
    have hnat : (1311664143 : ℕ)^8459*20000000000000^6411 ≤ 8539429897703^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311664143 2500000000 8539429897703 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141528073/250000000 : ℝ)^8459 ≤ (47202726229199/100000000000000 : ℝ)^6411 := by
    have hnat : (141528073 : ℕ)^8459*100000000000000^6411 ≤ 47202726229199^6411*250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141528073 250000000 47202726229199 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439873891/2500000000 : ℝ)^8459 ≤ (10100124263651/100000000000000 : ℝ)^6411 := by
    have hnat : (439873891 : ℕ)^8459*100000000000000^6411 ≤ 10100124263651^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439873891 2500000000 10100124263651 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311664143/2500000000 : ℝ), (141528073/250000000 : ℝ), (-439873891/2500000000 : ℝ)] ![(8539429897703/20000000000000 : ℝ), (47202726229199/100000000000000 : ℝ), (10100124263651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311664143/2500000000 : ℝ)|^8459 ≤ (8539429897703/20000000000000 : ℝ)^6411
        have hw : |(1311664143/2500000000 : ℝ)|=(1311664143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141528073/250000000 : ℝ)|^8459 ≤ (47202726229199/100000000000000 : ℝ)^6411
        have hw : |(141528073/250000000 : ℝ)|=(141528073/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439873891/2500000000 : ℝ)|^8459 ≤ (10100124263651/100000000000000 : ℝ)^6411
        have hw : |(-439873891/2500000000 : ℝ)|=(439873891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s1_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4308084119/10000000000 : ℝ)*x 0 + (4992017617/10000000000 : ℝ)*x 1 + (3717091039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308084119/10000000000 : ℝ)^8459 ≤ (32919703059247/100000000000000 : ℝ)^6411 := by
    have hnat : (4308084119 : ℕ)^8459*100000000000000^6411 ≤ 32919703059247^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308084119 10000000000 32919703059247 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992017617/10000000000 : ℝ)^8459 ≤ (39984358041289/100000000000000 : ℝ)^6411 := by
    have hnat : (4992017617 : ℕ)^8459*100000000000000^6411 ≤ 39984358041289^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992017617 10000000000 39984358041289 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3717091039/10000000000 : ℝ)^8459 ≤ (13547969438691/50000000000000 : ℝ)^6411 := by
    have hnat : (3717091039 : ℕ)^8459*50000000000000^6411 ≤ 13547969438691^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717091039 10000000000 13547969438691 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308084119/10000000000 : ℝ), (4992017617/10000000000 : ℝ), (3717091039/10000000000 : ℝ)] ![(32919703059247/100000000000000 : ℝ), (39984358041289/100000000000000 : ℝ), (13547969438691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308084119/10000000000 : ℝ)|^8459 ≤ (32919703059247/100000000000000 : ℝ)^6411
        have hw : |(4308084119/10000000000 : ℝ)|=(4308084119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992017617/10000000000 : ℝ)|^8459 ≤ (39984358041289/100000000000000 : ℝ)^6411
        have hw : |(4992017617/10000000000 : ℝ)|=(4992017617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3717091039/10000000000 : ℝ)|^8459 ≤ (13547969438691/50000000000000 : ℝ)^6411
        have hw : |(3717091039/10000000000 : ℝ)|=(3717091039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1579/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9949/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27347/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27347/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27347/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27347/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27347/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27347/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (913/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (377557688481/100000000000000000000 : ℝ) := by
    have hpowers : (913/100000 : ℝ)^4229 ≤ (377557688481/100000000000000000000 : ℝ)^1024 := by
      have hnat : (913 : ℕ)^4229*100000000000000000000^1024 ≤ 377557688481^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        913 100000 377557688481 100000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (913/100000 : ℝ)) (X := (377557688481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27347/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (472610111871268493/100000000000000000000 : ℝ) := by
    have hpowers : (27347/100000 : ℝ)^4229 ≤ (472610111871268493/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27347 : ℕ)^4229*100000000000000000000^1024 ≤ 472610111871268493^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27347 100000 472610111871268493 100000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27347/100000 : ℝ)) (X := (472610111871268493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000377557688481/50000000000000000000 : ℝ) ≤ (2000000003656837/2000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50000000377557688481/50000000000000000000 : ℝ)^1024 ≤ (2000000003656837/2000000000000000 : ℝ)^4229 := by
      have hnat : (50000000377557688481 : ℕ)^1024*2000000000000000^4229 ≤ 2000000003656837^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000377557688481 50000000000000000000 2000000003656837 2000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000003656837/2000000000000000 : ℝ)) (X := (50000000377557688481/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50236305244714478487/50000000000000000000 : ℝ) ≤ (5005711620206293/5000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50236305244714478487/50000000000000000000 : ℝ)^1024 ≤ (5005711620206293/5000000000000000 : ℝ)^4229 := by
      have hnat : (50236305244714478487 : ℕ)^1024*5000000000000000^4229 ≤ 5005711620206293^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50236305244714478487 50000000000000000000 5005711620206293 5000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005711620206293/5000000000000000 : ℝ)) (X := (50236305244714478487/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50472610111871268493/50000000000000000000 : ℝ) ≤ (10022846462540987/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50472610111871268493/50000000000000000000 : ℝ)^1024 ≤ (10022846462540987/10000000000000000 : ℝ)^4229 := by
      have hnat : (50472610111871268493 : ℕ)^1024*10000000000000000^4229 ≤ 10022846462540987^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50472610111871268493 50000000000000000000 10022846462540987 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022846462540987/10000000000000000 : ℝ)) (X := (50472610111871268493/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(377557688481/100000000000000000000 : ℝ) ≤ ((16519946354982355379/16521250000000000000 : ℝ)+2*(11423222128401/2643400000000000 : ℝ)*(913/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (16519946354982355379/16521250000000000000 : ℝ)+2*(11423222128401/2643400000000000 : ℝ)*(913/100000 : ℝ)=(2000000003656837/2000000000000000 : ℝ) by norm_num, show 1+2*(377557688481/100000000000000000000 : ℝ)=(50000000377557688481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(472610111871268493/100000000000000000000 : ℝ)+(377557688481/100000000000000000000 : ℝ) ≤ ((16519946354982355379/16521250000000000000 : ℝ)+(11423222128401/2643400000000000 : ℝ)*((27347/100000 : ℝ)+(913/100000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (16519946354982355379/16521250000000000000 : ℝ)+(11423222128401/2643400000000000 : ℝ)*((27347/100000 : ℝ)+(913/100000 : ℝ))=(5005711620206293/5000000000000000 : ℝ) by norm_num, show 1+(472610111871268493/100000000000000000000 : ℝ)+(377557688481/100000000000000000000 : ℝ)=(50236305244714478487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(472610111871268493/100000000000000000000 : ℝ) ≤ ((16519946354982355379/16521250000000000000 : ℝ)+2*(11423222128401/2643400000000000 : ℝ)*(27347/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (16519946354982355379/16521250000000000000 : ℝ)+2*(11423222128401/2643400000000000 : ℝ)*(27347/100000 : ℝ)=(10022846462540987/10000000000000000 : ℝ) by norm_num, show 1+2*(472610111871268493/100000000000000000000 : ℝ)=(50472610111871268493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16519946354982355379/16521250000000000000 : ℝ)*(X 1 0+X 2 0)+(11423222128401/2643400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (913/100000 : ℝ)) (hi := (27347/100000 : ℝ)) (c := (16519946354982355379/16521250000000000000 : ℝ)) (alpha := (11423222128401/2643400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16519946354982355379/16521250000000000000 : ℝ)*(X 0 1+X 2 1)+(11423222128401/2643400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (913/100000 : ℝ)) (hi := (27347/100000 : ℝ)) (c := (16519946354982355379/16521250000000000000 : ℝ)) (alpha := (11423222128401/2643400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16519946354982355379/16521250000000000000 : ℝ)*(X 0 2+X 1 2)+(11423222128401/2643400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (913/100000 : ℝ)) (hi := (27347/100000 : ℝ)) (c := (16519946354982355379/16521250000000000000 : ℝ)) (alpha := (11423222128401/2643400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-409767447/2000000000 : ℝ)*X 0 0+(5669640771/10000000000 : ℝ)*X 0 1+(5027177591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541236009/1000000000 : ℝ)*X 1 0+(-2393440319/10000000000 : ℝ)*X 1 1+(157099307/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412360301/10000000000 : ℝ)*X 2 0+(157099303/312500000 : ℝ)*X 2 1+(-2393440207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153381497/5000000000 : ℝ)*X 0 0+(739946251/2000000000 : ℝ)*X 0 1+(5009055919/10000000000 : ℝ)*X 0 2+(2153381497/5000000000 : ℝ)*X 1 0+(739946251/2000000000 : ℝ)*X 1 1+(5009055919/10000000000 : ℝ)*X 1 2+(2153381497/5000000000 : ℝ)*X 2 0+(739946251/2000000000 : ℝ)*X 2 1+(5009055919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-512371417/2500000000 : ℝ)*X 0 0+(5035538101/10000000000 : ℝ)*X 0 1+(1415280683/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((327916041/625000000 : ℝ)*X 1 0+(-1759494999/10000000000 : ℝ)*X 1 1+(1415280807/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311664143/2500000000 : ℝ)*X 2 0+(141528073/250000000 : ℝ)*X 2 1+(-439873891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308084119/10000000000 : ℝ)*X 0 0+(4992017617/10000000000 : ℝ)*X 0 1+(3717091039/10000000000 : ℝ)*X 0 2+(4308084119/10000000000 : ℝ)*X 1 0+(4992017617/10000000000 : ℝ)*X 1 1+(3717091039/10000000000 : ℝ)*X 1 2+(4308084119/10000000000 : ℝ)*X 2 0+(4992017617/10000000000 : ℝ)*X 2 1+(3717091039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136540210166045513263477887/103257812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (46039817/12500000000000 : ℝ)*(base19) + (426926357/100000000000000 : ℝ)*(base23) + (5973823/20000000000000 : ℝ)*(upper3) + (560893/50000000000000 : ℝ)*(upper4) + (21571449/25000000000000 : ℝ)*(upper5) + (1160135022934129/100000000000000 : ℝ)*(major0) + (1160135022934129/100000000000000 : ℝ)*(major1) + (1160135022934129/100000000000000 : ℝ)*(major2) + (155651160990459/10000000000000 : ℝ)*(sp0) + (1556514231686009/100000000000000 : ℝ)*(sp1) + (389128543269547/25000000000000 : ℝ)*(sp2) + (190938508446239/25000000000000 : ℝ)*(sp3) + (598019991/20000000000000 : ℝ)*(sp4) + (42750041/3125000000000 : ℝ)*(sp7) + (190938850446567/25000000000000 : ℝ)*(f.failure) + (311302920000909/20000000000000 : ℝ)*(f.sum) + (589665432662611/132170000000000000000000000000 : ℝ)*base66 + (3539876039964988859/1652125000000000000000000000000000 : ℝ)*base68 + (2985059179602613859/1652125000000000000000000000000000 : ℝ)*base70 + (5582770852257613859/1652125000000000000000000000000000 : ℝ)*base72 + (213322937208481/132170000000000000000000000000 : ℝ)*base74 + (522163189082136141/1652125000000000000000000000000000 : ℝ)*base75 + (4223458207735863859/1652125000000000000000000000000000 : ℝ)*base78 + (4023569507233863859/1652125000000000000000000000000000 : ℝ)*base80 + (204094352392991/132170000000000000000000000000 : ℝ)*base82 + (157951/500000000000000000000 : ℝ)*base89 + (157951/500000000000000000000 : ℝ)*base91 + (157951/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26154755259459640894953/5286800000000000000000000000 : ℝ) := by norm_num
    linear_combination (895066651/100000000000000 : ℝ)*(base19) + (422042233/50000000000000 : ℝ)*(base23) + (2639543/50000000000000 : ℝ)*(upper2) + (4535149/3125000000000 : ℝ)*(upper3) + (104160897/100000000000000 : ℝ)*(upper5) + (238286325070117/20000000000000 : ℝ)*(major0) + (238286325070117/20000000000000 : ℝ)*(major1) + (238286325070117/20000000000000 : ℝ)*(major2) + (203499811/4000000000000 : ℝ)*(sp1) + (792997033/20000000000000 : ℝ)*(sp2) + (1598504091598851/100000000000000 : ℝ)*(sp4) + (63939924361477/4000000000000 : ℝ)*(sp5) + (79924964126461/5000000000000 : ℝ)*(sp6) + (784358994196289/100000000000000 : ℝ)*(sp7) + (784358994196289/100000000000000 : ℝ)*(f.failure) + (1598504091598851/100000000000000 : ℝ)*(f.sum) + (16872699970067/5286800000000000000000000000 : ℝ)*base65 + (3164731990789359407/330425000000000000000000000000000 : ℝ)*base68 + (1687331161116565593/330425000000000000000000000000000 : ℝ)*base69 + (671902261037084407/330425000000000000000000000000000 : ℝ)*base72 + (657517951829/1057360000000000000000000000 : ℝ)*base74 + (566927865985165593/330425000000000000000000000000000 : ℝ)*base75 + (246556666157040593/330425000000000000000000000000000 : ℝ)*base77 + (241224205282184407/330425000000000000000000000000000 : ℝ)*base80 + (136988885611293/26434000000000000000000000000 : ℝ)*base81 + (6663383/2000000000000000000000 : ℝ)*base90 + (6663383/2000000000000000000000 : ℝ)*base92 + (6663383/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1266_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1579/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9949/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1266_s2_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-130980917/625000000 : ℝ)*x 0 + (109775119/200000000 : ℝ)*x 1 + (5178158617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130980917/625000000 : ℝ)^8459 ≤ (3180281845157/25000000000000 : ℝ)^6411 := by
    have hnat : (130980917 : ℕ)^8459*25000000000000^6411 ≤ 3180281845157^6411*625000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130980917 625000000 3180281845157 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109775119/200000000 : ℝ)^8459 ≤ (22657846143019/50000000000000 : ℝ)^6411 := by
    have hnat : (109775119 : ℕ)^8459*50000000000000^6411 ≤ 22657846143019^6411*200000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109775119 200000000 22657846143019 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178158617/10000000000 : ℝ)^8459 ≤ (2622698770279/6250000000000 : ℝ)^6411 := by
    have hnat : (5178158617 : ℕ)^8459*6250000000000^6411 ≤ 2622698770279^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178158617 10000000000 2622698770279 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130980917/625000000 : ℝ), (109775119/200000000 : ℝ), (5178158617/10000000000 : ℝ)] ![(3180281845157/25000000000000 : ℝ), (22657846143019/50000000000000 : ℝ), (2622698770279/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130980917/625000000 : ℝ)|^8459 ≤ (3180281845157/25000000000000 : ℝ)^6411
        have hw : |(-130980917/625000000 : ℝ)|=(130980917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109775119/200000000 : ℝ)|^8459 ≤ (22657846143019/50000000000000 : ℝ)^6411
        have hw : |(109775119/200000000 : ℝ)|=(109775119/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178158617/10000000000 : ℝ)|^8459 ≤ (2622698770279/6250000000000 : ℝ)^6411
        have hw : |(5178158617/10000000000 : ℝ)|=(5178158617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s2_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368719061/10000000000 : ℝ)*x 0 + (-2256449369/10000000000 : ℝ)*x 1 + (5178158843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368719061/10000000000 : ℝ)^8459 ≤ (22006329738601/50000000000000 : ℝ)^6411 := by
    have hnat : (5368719061 : ℕ)^8459*50000000000000^6411 ≤ 22006329738601^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368719061 10000000000 22006329738601 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256449369/10000000000 : ℝ)^8459 ≤ (2804831552689/20000000000000 : ℝ)^6411 := by
    have hnat : (2256449369 : ℕ)^8459*20000000000000^6411 ≤ 2804831552689^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256449369 10000000000 2804831552689 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178158843/10000000000 : ℝ)^8459 ≤ (2622698921313/6250000000000 : ℝ)^6411 := by
    have hnat : (5178158843 : ℕ)^8459*6250000000000^6411 ≤ 2622698921313^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178158843 10000000000 2622698921313 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368719061/10000000000 : ℝ), (-2256449369/10000000000 : ℝ), (5178158843/10000000000 : ℝ)] ![(22006329738601/50000000000000 : ℝ), (2804831552689/20000000000000 : ℝ), (2622698921313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368719061/10000000000 : ℝ)|^8459 ≤ (22006329738601/50000000000000 : ℝ)^6411
        have hw : |(5368719061/10000000000 : ℝ)|=(5368719061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2256449369/10000000000 : ℝ)|^8459 ≤ (2804831552689/20000000000000 : ℝ)^6411
        have hw : |(-2256449369/10000000000 : ℝ)|=(2256449369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178158843/10000000000 : ℝ)|^8459 ≤ (2622698921313/6250000000000 : ℝ)^6411
        have hw : |(5178158843/10000000000 : ℝ)|=(5178158843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s2_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342179751/2500000000 : ℝ)*x 0 + (1035631769/2000000000 : ℝ)*x 1 + (-1128224721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342179751/2500000000 : ℝ)^8459 ≤ (22006329430321/50000000000000 : ℝ)^6411 := by
    have hnat : (1342179751 : ℕ)^8459*50000000000000^6411 ≤ 22006329430321^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342179751 2500000000 22006329430321 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035631769/2000000000 : ℝ)^8459 ≤ (41963182762393/100000000000000 : ℝ)^6411 := by
    have hnat : (1035631769 : ℕ)^8459*100000000000000^6411 ≤ 41963182762393^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035631769 2000000000 41963182762393 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128224721/5000000000 : ℝ)^8459 ≤ (14024158362087/100000000000000 : ℝ)^6411 := by
    have hnat : (1128224721 : ℕ)^8459*100000000000000^6411 ≤ 14024158362087^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128224721 5000000000 14024158362087 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342179751/2500000000 : ℝ), (1035631769/2000000000 : ℝ), (-1128224721/5000000000 : ℝ)] ![(22006329430321/50000000000000 : ℝ), (41963182762393/100000000000000 : ℝ), (14024158362087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342179751/2500000000 : ℝ)|^8459 ≤ (22006329430321/50000000000000 : ℝ)^6411
        have hw : |(1342179751/2500000000 : ℝ)|=(1342179751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035631769/2000000000 : ℝ)|^8459 ≤ (41963182762393/100000000000000 : ℝ)^6411
        have hw : |(1035631769/2000000000 : ℝ)|=(1035631769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1128224721/5000000000 : ℝ)|^8459 ≤ (14024158362087/100000000000000 : ℝ)^6411
        have hw : |(-1128224721/5000000000 : ℝ)|=(1128224721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s2_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (867835839/2000000000 : ℝ)*x 0 + (806760887/2000000000 : ℝ)*x 1 + (2333396731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867835839/2000000000 : ℝ)^8459 ≤ (8308394417467/25000000000000 : ℝ)^6411 := by
    have hnat : (867835839 : ℕ)^8459*25000000000000^6411 ≤ 8308394417467^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867835839 2000000000 8308394417467 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806760887/2000000000 : ℝ)^8459 ≤ (6036567595291/20000000000000 : ℝ)^6411 := by
    have hnat : (806760887 : ℕ)^8459*20000000000000^6411 ≤ 6036567595291^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806760887 2000000000 6036567595291 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2333396731/5000000000 : ℝ)^8459 ≤ (36583584345757/100000000000000 : ℝ)^6411 := by
    have hnat : (2333396731 : ℕ)^8459*100000000000000^6411 ≤ 36583584345757^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2333396731 5000000000 36583584345757 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867835839/2000000000 : ℝ), (806760887/2000000000 : ℝ), (2333396731/5000000000 : ℝ)] ![(8308394417467/25000000000000 : ℝ), (6036567595291/20000000000000 : ℝ), (36583584345757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867835839/2000000000 : ℝ)|^8459 ≤ (8308394417467/25000000000000 : ℝ)^6411
        have hw : |(867835839/2000000000 : ℝ)|=(867835839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806760887/2000000000 : ℝ)|^8459 ≤ (6036567595291/20000000000000 : ℝ)^6411
        have hw : |(806760887/2000000000 : ℝ)|=(806760887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2333396731/5000000000 : ℝ)|^8459 ≤ (36583584345757/100000000000000 : ℝ)^6411
        have hw : |(2333396731/5000000000 : ℝ)|=(2333396731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s2_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095768239/10000000000 : ℝ)*x 0 + (1036024509/2000000000 : ℝ)*x 1 + (5486773909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095768239/10000000000 : ℝ)^8459 ≤ (795107287441/6250000000000 : ℝ)^6411 := by
    have hnat : (2095768239 : ℕ)^8459*6250000000000^6411 ≤ 795107287441^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095768239 10000000000 795107287441 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036024509/2000000000 : ℝ)^8459 ≤ (20992090618397/50000000000000 : ℝ)^6411 := by
    have hnat : (1036024509 : ℕ)^8459*50000000000000^6411 ≤ 20992090618397^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036024509 2000000000 20992090618397 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486773909/10000000000 : ℝ)^8459 ≤ (45294102142581/100000000000000 : ℝ)^6411 := by
    have hnat : (5486773909 : ℕ)^8459*100000000000000^6411 ≤ 45294102142581^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486773909 10000000000 45294102142581 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095768239/10000000000 : ℝ), (1036024509/2000000000 : ℝ), (5486773909/10000000000 : ℝ)] ![(795107287441/6250000000000 : ℝ), (20992090618397/50000000000000 : ℝ), (45294102142581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095768239/10000000000 : ℝ)|^8459 ≤ (795107287441/6250000000000 : ℝ)^6411
        have hw : |(-2095768239/10000000000 : ℝ)|=(2095768239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036024509/2000000000 : ℝ)|^8459 ≤ (20992090618397/50000000000000 : ℝ)^6411
        have hw : |(1036024509/2000000000 : ℝ)|=(1036024509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486773909/10000000000 : ℝ)|^8459 ≤ (45294102142581/100000000000000 : ℝ)^6411
        have hw : |(5486773909/10000000000 : ℝ)|=(5486773909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s2_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057856673/2000000000 : ℝ)*x 0 + (-243479253/1250000000 : ℝ)*x 1 + (85730843/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057856673/2000000000 : ℝ)^8459 ≤ (10788863553967/25000000000000 : ℝ)^6411 := by
    have hnat : (1057856673 : ℕ)^8459*25000000000000^6411 ≤ 10788863553967^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057856673 2000000000 10788863553967 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243479253/1250000000 : ℝ)^8459 ≤ (2887610787359/25000000000000 : ℝ)^6411 := by
    have hnat : (243479253 : ℕ)^8459*25000000000000^6411 ≤ 2887610787359^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243479253 1250000000 2887610787359 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85730843/156250000 : ℝ)^8459 ≤ (11323525652737/25000000000000 : ℝ)^6411 := by
    have hnat : (85730843 : ℕ)^8459*25000000000000^6411 ≤ 11323525652737^6411*156250000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85730843 156250000 11323525652737 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057856673/2000000000 : ℝ), (-243479253/1250000000 : ℝ), (85730843/156250000 : ℝ)] ![(10788863553967/25000000000000 : ℝ), (2887610787359/25000000000000 : ℝ), (11323525652737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057856673/2000000000 : ℝ)|^8459 ≤ (10788863553967/25000000000000 : ℝ)^6411
        have hw : |(1057856673/2000000000 : ℝ)|=(1057856673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243479253/1250000000 : ℝ)|^8459 ≤ (2887610787359/25000000000000 : ℝ)^6411
        have hw : |(-243479253/1250000000 : ℝ)|=(243479253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85730843/156250000 : ℝ)|^8459 ≤ (11323525652737/25000000000000 : ℝ)^6411
        have hw : |(85730843/156250000 : ℝ)|=(85730843/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s2_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132232087/250000000 : ℝ)*x 0 + (548677407/1000000000 : ℝ)*x 1 + (-1947833703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132232087/250000000 : ℝ)^8459 ≤ (8631091090779/20000000000000 : ℝ)^6411 := by
    have hnat : (132232087 : ℕ)^8459*20000000000000^6411 ≤ 8631091090779^6411*250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132232087 250000000 8631091090779 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548677407/1000000000 : ℝ)^8459 ≤ (9058820779247/20000000000000 : ℝ)^6411 := by
    have hnat : (548677407 : ℕ)^8459*20000000000000^6411 ≤ 9058820779247^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548677407 1000000000 9058820779247 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947833703/10000000000 : ℝ)^8459 ≤ (11550440637867/100000000000000 : ℝ)^6411 := by
    have hnat : (1947833703 : ℕ)^8459*100000000000000^6411 ≤ 11550440637867^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947833703 10000000000 11550440637867 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132232087/250000000 : ℝ), (548677407/1000000000 : ℝ), (-1947833703/10000000000 : ℝ)] ![(8631091090779/20000000000000 : ℝ), (9058820779247/20000000000000 : ℝ), (11550440637867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132232087/250000000 : ℝ)|^8459 ≤ (8631091090779/20000000000000 : ℝ)^6411
        have hw : |(132232087/250000000 : ℝ)|=(132232087/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548677407/1000000000 : ℝ)|^8459 ≤ (9058820779247/20000000000000 : ℝ)^6411
        have hw : |(548677407/1000000000 : ℝ)|=(548677407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947833703/10000000000 : ℝ)|^8459 ≤ (11550440637867/100000000000000 : ℝ)^6411
        have hw : |(-1947833703/10000000000 : ℝ)|=(1947833703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s2_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4339328709/10000000000 : ℝ)*x 0 + (1165697889/2500000000 : ℝ)*x 1 + (403784283/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339328709/10000000000 : ℝ)^8459 ≤ (33235088609141/100000000000000 : ℝ)^6411 := by
    have hnat : (4339328709 : ℕ)^8459*100000000000000^6411 ≤ 33235088609141^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339328709 10000000000 33235088609141 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165697889/2500000000 : ℝ)^8459 ≤ (7308439386107/20000000000000 : ℝ)^6411 := by
    have hnat : (1165697889 : ℕ)^8459*20000000000000^6411 ≤ 7308439386107^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165697889 2500000000 7308439386107 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403784283/1000000000 : ℝ)^8459 ≤ (944459826441/3125000000000 : ℝ)^6411 := by
    have hnat : (403784283 : ℕ)^8459*3125000000000^6411 ≤ 944459826441^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403784283 1000000000 944459826441 3125000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339328709/10000000000 : ℝ), (1165697889/2500000000 : ℝ), (403784283/1000000000 : ℝ)] ![(33235088609141/100000000000000 : ℝ), (7308439386107/20000000000000 : ℝ), (944459826441/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339328709/10000000000 : ℝ)|^8459 ≤ (33235088609141/100000000000000 : ℝ)^6411
        have hw : |(4339328709/10000000000 : ℝ)|=(4339328709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1165697889/2500000000 : ℝ)|^8459 ≤ (7308439386107/20000000000000 : ℝ)^6411
        have hw : |(1165697889/2500000000 : ℝ)|=(1165697889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403784283/1000000000 : ℝ)|^8459 ≤ (944459826441/3125000000000 : ℝ)^6411
        have hw : |(403784283/1000000000 : ℝ)|=(403784283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2399/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16161/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9949/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1579/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9949/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1579/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9949/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1579/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9949/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1579/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9949/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1579/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9949/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1579/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1579/25000 : ℝ) ^ (4229/1024 : ℝ) ≤ (555823031599297/50000000000000000000 : ℝ) := by
    have hpowers : (1579/25000 : ℝ)^4229 ≤ (555823031599297/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1579 : ℕ)^4229*50000000000000000000^1024 ≤ 555823031599297^1024*25000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1579 25000 555823031599297 50000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1579/25000 : ℝ)) (X := (555823031599297/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9949/50000 : ℝ) ^ (4229/1024 : ℝ) ≤ (25421144425142737/20000000000000000000 : ℝ) := by
    have hpowers : (9949/50000 : ℝ)^4229 ≤ (25421144425142737/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9949 : ℕ)^4229*20000000000000000000^1024 ≤ 25421144425142737^1024*50000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9949 50000 25421144425142737 20000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9949/50000 : ℝ)) (X := (25421144425142737/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000555823031599297/25000000000000000000 : ℝ) ≤ (2000010766762627/2000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (25000555823031599297/25000000000000000000 : ℝ)^1024 ≤ (2000010766762627/2000000000000000 : ℝ)^4229 := by
      have hnat : (25000555823031599297 : ℕ)^1024*2000000000000000^4229 ≤ 2000010766762627^4229*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000555823031599297 25000000000000000000 2000010766762627 2000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000010766762627/2000000000000000 : ℝ)) (X := (25000555823031599297/25000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100128217368188912279/100000000000000000000 : ℝ) ≤ (100031031175857/100000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (100128217368188912279/100000000000000000000 : ℝ)^1024 ≤ (100031031175857/100000000000000 : ℝ)^4229 := by
      have hnat : (100128217368188912279 : ℕ)^1024*100000000000000^4229 ≤ 100031031175857^4229*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100128217368188912279 100000000000000000000 100031031175857 100000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100031031175857/100000000000000 : ℝ)) (X := (100128217368188912279/100000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10025421144425142737/10000000000000000000 : ℝ) ≤ (2001230480271653/2000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (10025421144425142737/10000000000000000000 : ℝ)^1024 ≤ (2001230480271653/2000000000000000 : ℝ)^4229 := by
      have hnat : (10025421144425142737 : ℕ)^1024*2000000000000000^4229 ≤ 2001230480271653^4229*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10025421144425142737 10000000000000000000 2001230480271653 2000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001230480271653/2000000000000000 : ℝ)) (X := (10025421144425142737/10000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(555823031599297/50000000000000000000 : ℝ) ≤ ((13578221261823495849/13582000000000000000 : ℝ)+2*(609856754513/271640000000000 : ℝ)*(1579/25000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (13578221261823495849/13582000000000000000 : ℝ)+2*(609856754513/271640000000000 : ℝ)*(1579/25000 : ℝ)=(2000010766762627/2000000000000000 : ℝ) by norm_num, show 1+2*(555823031599297/50000000000000000000 : ℝ)=(25000555823031599297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25421144425142737/20000000000000000000 : ℝ)+(555823031599297/50000000000000000000 : ℝ) ≤ ((13578221261823495849/13582000000000000000 : ℝ)+(609856754513/271640000000000 : ℝ)*((9949/50000 : ℝ)+(1579/25000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (13578221261823495849/13582000000000000000 : ℝ)+(609856754513/271640000000000 : ℝ)*((9949/50000 : ℝ)+(1579/25000 : ℝ))=(100031031175857/100000000000000 : ℝ) by norm_num, show 1+(25421144425142737/20000000000000000000 : ℝ)+(555823031599297/50000000000000000000 : ℝ)=(100128217368188912279/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25421144425142737/20000000000000000000 : ℝ) ≤ ((13578221261823495849/13582000000000000000 : ℝ)+2*(609856754513/271640000000000 : ℝ)*(9949/50000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (13578221261823495849/13582000000000000000 : ℝ)+2*(609856754513/271640000000000 : ℝ)*(9949/50000 : ℝ)=(2001230480271653/2000000000000000 : ℝ) by norm_num, show 1+2*(25421144425142737/20000000000000000000 : ℝ)=(10025421144425142737/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13578221261823495849/13582000000000000000 : ℝ)*(X 1 0+X 2 0)+(609856754513/271640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (1579/25000 : ℝ)) (hi := (9949/50000 : ℝ)) (c := (13578221261823495849/13582000000000000000 : ℝ)) (alpha := (609856754513/271640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13578221261823495849/13582000000000000000 : ℝ)*(X 0 1+X 2 1)+(609856754513/271640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (1579/25000 : ℝ)) (hi := (9949/50000 : ℝ)) (c := (13578221261823495849/13582000000000000000 : ℝ)) (alpha := (609856754513/271640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13578221261823495849/13582000000000000000 : ℝ)*(X 0 2+X 1 2)+(609856754513/271640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (1579/25000 : ℝ)) (hi := (9949/50000 : ℝ)) (c := (13578221261823495849/13582000000000000000 : ℝ)) (alpha := (609856754513/271640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-130980917/625000000 : ℝ)*X 0 0+(109775119/200000000 : ℝ)*X 0 1+(5178158617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368719061/10000000000 : ℝ)*X 1 0+(-2256449369/10000000000 : ℝ)*X 1 1+(5178158843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342179751/2500000000 : ℝ)*X 2 0+(1035631769/2000000000 : ℝ)*X 2 1+(-1128224721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867835839/2000000000 : ℝ)*X 0 0+(806760887/2000000000 : ℝ)*X 0 1+(2333396731/5000000000 : ℝ)*X 0 2+(867835839/2000000000 : ℝ)*X 1 0+(806760887/2000000000 : ℝ)*X 1 1+(2333396731/5000000000 : ℝ)*X 1 2+(867835839/2000000000 : ℝ)*X 2 0+(806760887/2000000000 : ℝ)*X 2 1+(2333396731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2095768239/10000000000 : ℝ)*X 0 0+(1036024509/2000000000 : ℝ)*X 0 1+(5486773909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057856673/2000000000 : ℝ)*X 1 0+(-243479253/1250000000 : ℝ)*X 1 1+(85730843/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132232087/250000000 : ℝ)*X 2 0+(548677407/1000000000 : ℝ)*X 2 1+(-1947833703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339328709/10000000000 : ℝ)*X 0 0+(1165697889/2500000000 : ℝ)*X 0 1+(403784283/1000000000 : ℝ)*X 0 2+(4339328709/10000000000 : ℝ)*X 1 0+(1165697889/2500000000 : ℝ)*X 1 1+(403784283/1000000000 : ℝ)*X 1 2+(4339328709/10000000000 : ℝ)*X 2 0+(1165697889/2500000000 : ℝ)*X 2 1+(403784283/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1784420794869647254851167271/679100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348857457/100000000000000 : ℝ)*(base19) + (313771879/100000000000000 : ℝ)*(base23) + (37748863/50000000000000 : ℝ)*(upper3) + (484659/100000000000000 : ℝ)*(upper4) + (8038359/50000000000000 : ℝ)*(upper5) + (2399712651128293/100000000000000 : ℝ)*(major0) + (2399712651128293/100000000000000 : ℝ)*(major1) + (2399712651128293/100000000000000 : ℝ)*(major2) + (402451168074171/12500000000000 : ℝ)*(sp0) + (1609807178861007/50000000000000 : ℝ)*(sp1) + (402451799100949/12500000000000 : ℝ)*(sp2) + (394952031530013/25000000000000 : ℝ)*(sp3) + (670248263/12500000000000 : ℝ)*(sp4) + (95278781/4000000000000 : ℝ)*(sp7) + (1579810508089577/100000000000000 : ℝ)*(f.failure) + (3219614706579471/100000000000000 : ℝ)*(f.sum) + (70791940093343/13582000000000000000000000000 : ℝ)*base65 + (584200605292594243/1358200000000000000000000000000000 : ℝ)*base68 + (9672803120433794243/1358200000000000000000000000000000 : ℝ)*base70 + (1269464752821605757/1358200000000000000000000000000000 : ℝ)*base71 + (34228827464281/13582000000000000000000000000 : ℝ)*base73 + (3441187583055794243/1358200000000000000000000000000000 : ℝ)*base76 + (68049201093194243/1358200000000000000000000000000000 : ℝ)*base78 + (6681766063635405757/1358200000000000000000000000000000 : ℝ)*base79 + (19651506501711/13582000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8865519/2000000000000000000000 : ℝ)*base90 + (8865519/2000000000000000000000 : ℝ)*base92 + (8865519/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1267834596049982635050378537/679100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7677547/1000000000000 : ℝ)*(base19) + (1074030393/100000000000000 : ℝ)*(base23) + (36119347/50000000000000 : ℝ)*(upper2) + (129637307/100000000000000 : ℝ)*(upper3) + (15268957/50000000000000 : ℝ)*(upper5) + (2430581109164171/100000000000000 : ℝ)*(major0) + (2430581109164171/100000000000000 : ℝ)*(major1) + (2430581109164171/100000000000000 : ℝ)*(major2) + (7481492809/100000000000000 : ℝ)*(sp1) + (7030049057/50000000000000 : ℝ)*(sp2) + (3261029917257637/100000000000000 : ℝ)*(sp4) + (3261021668010129/100000000000000 : ℝ)*(sp5) + (326101478312913/10000000000000 : ℝ)*(sp6) + (1600132238839579/100000000000000 : ℝ)*(sp7) + (1600132238839579/100000000000000 : ℝ)*(f.failure) + (3261029917257637/100000000000000 : ℝ)*(f.sum) + (13206080189747/13582000000000000000000000000 : ℝ)*base65 + (4660249613715623821/1358200000000000000000000000000000 : ℝ)*base68 + (2913561840169576179/1358200000000000000000000000000000 : ℝ)*base69 + (3270795877934823821/1358200000000000000000000000000000 : ℝ)*base72 + (38801412988049/13582000000000000000000000000 : ℝ)*base73 + (15708754707978823821/1358200000000000000000000000000000 : ℝ)*base76 + (1661922458104776179/1358200000000000000000000000000000 : ℝ)*base77 + (24388717521838623821/1358200000000000000000000000000000 : ℝ)*base80 + (65165847642779/13582000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3356013/2000000000000000000000 : ℝ)*base90 + (3356013/2000000000000000000000 : ℝ)*base92 + (3356013/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1266_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2399/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16161/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1266_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2399/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16161/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1266_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1266_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1266_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2399/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16161/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1266_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
