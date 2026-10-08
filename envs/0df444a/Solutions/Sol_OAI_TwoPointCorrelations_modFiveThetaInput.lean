-- Prove2me | solution 1 for OAI.TwoPointCorrelations.modFiveThetaInput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:17:55.802393+00:00
-- url     : https://prove2.me/submissions/db4d9e39-3211-4e79-a86a-327e497000f1

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_modFive_smoothed_contour_bound
import Theorems.Thm_OAI_TwoPointCorrelations_modFive_zeta_psi_decay

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveMangoldt
namespace OAI

/-! Exact finite reductions for the fixed modulus-five prime input.

The only primes-versus-prime-powers loss is the existing elementary
Chebyshev bound. These identities convert (preTransparency := .instances) quantitative Dirichlet L-function
estimates into the selected logarithmically weighted prime estimates.
-/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.BigOperators _root_.Classical





lemma modFivePrime_iff (one : Bool) (n : ℕ) :
    ModFivePrime one n ↔ n.Prime ∧ modFiveResidue one n := by
  rfl

lemma modFive_logWeight_eq (one : Bool) (n : ℕ) :
    modFiveLogWeight one n =
      if modFiveResidue one n then (if n.Prime then Real.log n else 0) else 0 := by
  by_cases hp : n.Prime <;> by_cases hr : modFiveResidue one n <;>
    simp [modFiveLogWeight, modFivePrime_iff, hp, hr]

lemma modFive_weight_difference (one : Bool) (n : ℕ) :
    modFiveMangoldtWeight one n - modFiveLogWeight one n =
      if modFiveResidue one n ∧ ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
  rw [modFive_logWeight_eq]
  by_cases hp : n.Prime
  · simp [modFiveMangoldtWeight, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · by_cases hr : modFiveResidue one n <;> simp [modFiveMangoldtWeight, hp, hr]

lemma modFive_weight_difference_nonneg (one : Bool) (n : ℕ) :
    0 ≤ modFiveMangoldtWeight one n - modFiveLogWeight one n := by
  rw [modFive_weight_difference]
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · rfl

lemma modFive_weight_difference_le (one : Bool) (n : ℕ) :
    modFiveMangoldtWeight one n - modFiveLogWeight one n ≤
      ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log n else 0) := by
  rw [modFive_weight_difference]
  by_cases hp : n.Prime
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp only [hp, ↓reduceIte, sub_zero]
    split_ifs
    · rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg

/-- Restricting the prime-power error to either selection cannot increase it. -/
theorem modFivePsi_sub_theta_bounds (one : Bool) (x : ℝ) :
    0 ≤ modFivePsi one x - modFiveTheta one x ∧
      modFivePsi one x - modFiveTheta one x ≤ Chebyshev.psi x - Chebyshev.theta x := by
  have hsum : modFivePsi one x - modFiveTheta one x =
      ∑ n ∈ Icc 0 ⌊x⌋₊,
        (modFiveMangoldtWeight one n - modFiveLogWeight one n) := by
    simp only [modFivePsi, modFiveTheta, sum_sub_distrib]
  rw [hsum]
  constructor
  · exact sum_nonneg fun n _ => modFive_weight_difference_nonneg one n
  · rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, sum_filter,
      ← sum_sub_distrib]
    exact sum_le_sum fun n _ => modFive_weight_difference_le one n

/-- The elementary loss in passing from a von Mangoldt estimate to primes. -/
theorem modFivePsi_sub_theta_abs_le (one : Bool) {x : ℝ} (hx : 1 ≤ x) :
    |modFivePsi one x - modFiveTheta one x| ≤ 2 * Real.sqrt x * Real.log x := by
  rw [abs_of_nonneg (modFivePsi_sub_theta_bounds one x).1]
  exact (modFivePsi_sub_theta_bounds one x).2.trans (Chebyshev.psi_sub_theta_le hx)

lemma modFiveMangoldtWeight_complement (n : ℕ) :
    modFiveMangoldtWeight false n + modFiveMangoldtWeight true n =
      ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n % 5 = 1 <;> simp [modFiveMangoldtWeight, modFiveResidue, hn]

lemma modFivePsi_complement (x : ℝ) :
    modFivePsi false x + modFivePsi true x = Chebyshev.psi x := by
  rw [modFivePsi, modFivePsi, ← sum_add_distrib, Chebyshev.psi_eq_sum_Icc]
  exact sum_congr rfl fun n _ => modFiveMangoldtWeight_complement n

lemma modFive_character_sum (n : ℕ) :
    (∑ χ : DirichletCharacter ℂ 5, χ (n : ZMod 5)) =
      if n % 5 = 1 then (4 : ℂ) else 0 := by
  have heq : (n : ZMod 5) = 1 ↔ n % 5 = 1 := by
    simpa only [Nat.cast_one, Nat.mod_eq_of_lt (by decide : 1 < 5)] using
      (ZMod.natCast_eq_natCast_iff' n 1 5)
  simp only [DirichletCharacter.sum_characters_eq, heq]
  norm_num [Nat.totient_prime (by decide : Nat.Prime 5)]

/-- Exact character expansion; no asymptotic input is used here. -/
theorem modFivePsi_true_character_sum (x : ℝ) :
    (4 : ℂ) * (modFivePsi true x : ℂ) =
      ∑ χ : DirichletCharacter ℂ 5, modFiveTwistedPsi χ x := by
  simp only [modFivePsi, modFiveTwistedPsi, Complex.ofReal_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [← mul_sum, modFive_character_sum]
  by_cases h : n % 5 = 1 <;>
    simp [modFiveMangoldtWeight, modFiveResidue, h, mul_comm]

lemma sqrt_mul_log_le_exp_sqrt (c : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x * Real.log x ≤
      4 * Real.exp (c ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hy : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsquare := sq_nonneg (Real.sqrt (Real.log x) / 2 - c)
  have hsqrt := Real.sq_sqrt hy
  have hcs : c * Real.sqrt (Real.log x) ≤ Real.log x / 4 + c ^ 2 := by
    nlinarith
  have hlog : Real.log x ≤ 4 * Real.exp (Real.log x / 4) := by
    have he := Real.add_one_le_exp (Real.log x / 4)
    linarith
  have hexp : Real.exp (-Real.log x / 4) ≤
      Real.exp (c ^ 2) * Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hid : Real.sqrt x * Real.exp (Real.log x / 4) =
      x * Real.exp (-Real.log x / 4) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxp]
    conv_rhs => lhs; rw [← Real.exp_log hxp]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.sqrt x * Real.log x ≤ Real.sqrt x * (4 * Real.exp (Real.log x / 4)) :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    _ = 4 * (x * Real.exp (-Real.log x / 4)) := by rw [← hid]; ring
    _ ≤ 4 * (x * (Real.exp (c ^ 2) *
        Real.exp (-c * Real.sqrt (Real.log x)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp hxp.le) (by norm_num)
    _ = _ := by ring

/-- A quantitative estimate for the selected von Mangoldt sums gives the
exact prime estimate used by the application, with unchanged exponent. -/
theorem modFiveThetaInput_of_psi (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hpsi : ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |modFivePsi one x - modFiveDensity one * x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    ModFiveThetaInput := by
  refine ⟨c, C + 8 * Real.exp (c ^ 2), hc, by positivity, ?_⟩
  intro one x hx
  have herr := modFivePsi_sub_theta_abs_le one (show 1 ≤ x by linarith)
  have habsorb := sqrt_mul_log_le_exp_sqrt c (show 1 ≤ x by linarith)
  calc
    |modFiveTheta one x - modFiveDensity one * x| =
        |(modFivePsi one x - modFiveDensity one * x) -
          (modFivePsi one x - modFiveTheta one x)| := by congr 1; ring
    _ ≤ |modFivePsi one x - modFiveDensity one * x| +
        |modFivePsi one x - modFiveTheta one x| := abs_sub _ _
    _ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) +
        2 * (Real.sqrt x * Real.log x) := by
      exact add_le_add (hpsi one x hx) (by simpa [mul_assoc] using herr)
    _ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) +
        2 * (4 * Real.exp (c ^ 2) * x *
          Real.exp (-c * Real.sqrt (Real.log x))) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left habsorb (show (0 : ℝ) ≤ 2 by norm_num))
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveInputExtension
namespace OAI

/-! Finite-cutoff completion of the fixed modulus-five prime input.
An eventual quantitative Mangoldt estimate suffices, since the remaining
bounded cutoffs are controlled by one finite nonnegative Mangoldt sum. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

lemma modFivePsi_nonneg (one : Bool) (x : ℝ) : 0 ≤ modFivePsi one x := by
  apply sum_nonneg
  intro n hn
  unfold modFiveMangoldtWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · rfl

lemma modFivePsi_le_psi (one : Bool) {x y : ℝ} (hxy : x ≤ y) :
    modFivePsi one x ≤ Chebyshev.psi y := by
  rw [modFivePsi, Chebyshev.psi_eq_sum_Icc]
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
      apply sum_le_sum
      intro n hn
      unfold modFiveMangoldtWeight
      split_ifs
      · rfl
      · exact ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc_right (Nat.floor_le_floor hxy))
      (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma modFiveDensity_bounds (one : Bool) : 0 ≤ modFiveDensity one ∧ modFiveDensity one ≤ 1 := by
  cases one <;> norm_num [modFiveDensity]

lemma modFivePsi_bounded_cutoffs (one : Bool) {x Y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ Y) :
    |modFivePsi one x - modFiveDensity one * x| ≤ Chebyshev.psi Y + Y := by
  have hd := modFiveDensity_bounds one
  have hm : 0 ≤ modFiveDensity one * x := mul_nonneg hd.1 hx
  calc
    _ ≤ |modFivePsi one x| + |modFiveDensity one * x| := abs_sub _ _
    _ = modFivePsi one x + modFiveDensity one * x := by
      rw [abs_of_nonneg (modFivePsi_nonneg one x), abs_of_nonneg hm]
    _ ≤ _ := add_le_add (modFivePsi_le_psi one hxy)
      ((mul_le_mul_of_nonneg_right hd.2 hx).trans_eq (one_mul x) |>.trans hxy)

theorem modFiveThetaInput_of_eventual_psi (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hbound : ∀ᶠ x : ℝ in atTop, ∀ one : Bool,
      |modFivePsi one x - modFiveDensity one * x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    ModFiveThetaInput := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp hbound
  let Y := max 2 X
  let M := Chebyshev.psi Y + Y
  let K := M * Real.exp (c * Real.sqrt (Real.log Y))
  have hY2 : 2 ≤ Y := le_max_left _ _
  have hM : 0 ≤ M := add_nonneg (Chebyshev.psi_nonneg _) (by dsimp [Y]; positivity)
  have hK : 0 ≤ K := mul_nonneg hM (Real.exp_pos _).le
  apply modFiveThetaInput_of_psi c (max C K) hc (hC.trans (le_max_left _ _))
  intro one x hx
  by_cases hlarge : Y ≤ x
  · exact (hX x ((le_max_right _ _).trans hlarge) one).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C K)
        (by linarith)) (Real.exp_pos _).le)
  · have hxy : x ≤ Y := (lt_of_not_ge hlarge).le
    have hnorm := modFivePsi_bounded_cutoffs one (by linarith) hxy
    have hroot : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log Y) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hxy)
    have hexp : Real.exp (-c * Real.sqrt (Real.log Y)) ≤
        Real.exp (-c * Real.sqrt (Real.log x)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hroot (neg_nonpos.mpr hc.le))
    have hprod : 1 ≤ Real.exp (c * Real.sqrt (Real.log Y)) *
        Real.exp (-c * Real.sqrt (Real.log x)) := by
      calc
        1 = Real.exp (c * Real.sqrt (Real.log Y)) *
            Real.exp (-c * Real.sqrt (Real.log Y)) := by rw [← Real.exp_add]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    have hm : M ≤ K * Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hh := mul_le_mul_of_nonneg_left hprod hM
      simpa only [mul_one, K, mul_assoc] using hh
    apply hnorm.trans (hm.trans ?_)
    calc
      K * Real.exp (-c * Real.sqrt (Real.log x)) ≤
          (K * x) * Real.exp (-c * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (by linarith : 1 ≤ x) hK)
          (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right C K) (by linarith)) (Real.exp_pos _).le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩











lemma modFiveTwistedPsi_eq (χ : DirichletCharacter ℂ 5) (x : ℝ) :
    modFiveTwistedPsi χ x = ∑ n ∈ Icc 0 ⌊x⌋₊, modFiveMangoldtTwist χ n := by
  unfold modFiveTwistedPsi modFiveMangoldtTwist
  exact sum_congr rfl fun n _ => mul_comm _ _




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveUnsmoothing
namespace OAI

/-! Exact finite differences for the triangularly smoothed Mangoldt sum.
The error is confined to the short interval at the upper endpoint. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset _root_.ArithmeticFunction
open scoped _root_.BigOperators

lemma modFive_smoothed_scale (χ : DirichletCharacter ℂ 5) {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) * modFiveSmoothedPsi χ x =
      ∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n * ((x - (n : ℝ) : ℝ) : ℂ) := by
  rw [modFiveSmoothedPsi, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  push_cast
  field_simp

lemma modFive_smoothed_difference (χ : DirichletCharacter ℂ 5) {x : ℝ}
    (hx : 0 < x) (m : ℕ) :
    (((x + m : ℝ) : ℂ) * modFiveSmoothedPsi χ (x + m) -
      (x : ℂ) * modFiveSmoothedPsi χ x) =
      (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n) +
        ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
          modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ) := by
  rw [modFive_smoothed_scale χ (by positivity), modFive_smoothed_scale χ hx.ne',
    Nat.floor_add_natCast hx.le]
  have hsplit (f : ℕ → ℂ) :
      (∑ n ∈ Icc 1 (⌊x⌋₊ + m), f n) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, f n) + (∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), f n) := by
    simpa only [Ico_add_one_right_eq_Icc] using
      (sum_Ico_consecutive f (by omega : 1 ≤ ⌊x⌋₊ + 1)
        (by omega : ⌊x⌋₊ + 1 ≤ (⌊x⌋₊ + m) + 1)).symm
  rw [hsplit]
  have hmain :
      (∑ n ∈ Icc 1 ⌊x⌋₊,
        modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)) -
      (∑ n ∈ Icc 1 ⌊x⌋₊,
        modFiveMangoldtTwist χ n * ((x - (n : ℝ) : ℝ) : ℂ)) =
      (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n) := by
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro n hn
    push_cast
    ring
  linear_combination hmain

lemma modFive_mangoldt_norm_le_log (χ : DirichletCharacter ℂ 5) (n : ℕ) : ‖modFiveMangoldtTwist χ n‖ ≤ Real.log (n : ℝ) := by
  unfold modFiveMangoldtTwist
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) vonMangoldt_nonneg).trans
    (by simpa using (vonMangoldt_le_log (n := n)))

lemma modFive_smoothed_remainder (χ : DirichletCharacter ℂ 5) {x : ℝ}
    (hx : 0 < x) (m : ℕ) :
    ‖∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
      modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤
        (m : ℝ) ^ 2 * Real.log (x + m) := by
  have hy : 0 < x + (m : ℝ) := by positivity
  have hpoint (n : ℕ) (hn : n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) :
      ‖modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤
        Real.log (x + m) * m := by
    obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hnx : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hnlo)
    have hny : (n : ℝ) ≤ x + m := by
      have hb := Nat.floor_le hx.le
      have hc : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) + m := by exact_mod_cast hnhi
      linarith
    have hwt : 0 ≤ x + m - (n : ℝ) := by linarith
    have hwtm : x + m - (n : ℝ) ≤ (m : ℝ) := by linarith
    have hlog : ‖modFiveMangoldtTwist χ n‖ ≤ Real.log (x + m) :=
      (modFive_mangoldt_norm_le_log χ n).trans
        (Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hny)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwt]
    exact mul_le_mul hlog hwtm hwt (le_trans (norm_nonneg _) hlog)
  have hc : #(Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) = m := by
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        ‖modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), Real.log (x + m) * m :=
      sum_le_sum hpoint
    _ = _ := by rw [sum_const, hc, nsmul_eq_mul]; ring

lemma modFive_twistedPsi_sum (χ : DirichletCharacter ℂ 5) (x : ℝ) :
    modFiveTwistedPsi χ x = ∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n := by
  have he : (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n) =
      ∑ n ∈ Icc 0 ⌊x⌋₊, modFiveMangoldtTwist χ n := by
    apply sum_subset
    · intro n hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
      exact mem_Icc.mpr ⟨by omega, hnN⟩
    · intro n hn hnot
      have hn0 : n = 0 := by
        have := mem_Icc.mp hn
        have hn1 : ¬1 ≤ n := by
          intro hn1
          exact hnot (mem_Icc.mpr ⟨hn1, this.2⟩)
        omega
      subst n
      simp [modFiveMangoldtTwist]
  rw [he, modFiveTwistedPsi]
  apply sum_congr rfl
  intro n hn
  simp only [modFiveMangoldtTwist, mul_comm]

/-- A completely finite unsmoothing inequality, with the short-interval
cost bounded only by the elementary Mangoldt estimate Λ(n)≤ log n. -/
theorem modFive_unsmoothing_bound (χ : DirichletCharacter ℂ 5) {x : ℝ}
    (hx : 0 < x) {m : ℕ} (hm : 0 < m) :
    ‖modFiveTwistedPsi χ x‖ ≤
      ((x + m) * ‖modFiveSmoothedPsi χ (x + m)‖ +
        x * ‖modFiveSmoothedPsi χ x‖ + (m : ℝ) ^ 2 * Real.log (x + m)) / m := by
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have he := modFive_smoothed_difference χ hx m
  have halg : (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n) =
      (((x + m : ℝ) : ℂ) * modFiveSmoothedPsi χ (x + m) -
        (x : ℂ) * modFiveSmoothedPsi χ x) -
      ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ) := by
    linear_combination -he
  rw [modFive_twistedPsi_sum]
  apply (le_div_iff₀ hmp).mpr
  calc
    _ = ‖(m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n)‖ := by
      rw [norm_mul, Complex.norm_natCast]
      ring
    _ ≤ ‖((x + m : ℝ) : ℂ) * modFiveSmoothedPsi χ (x + m) -
        (x : ℂ) * modFiveSmoothedPsi χ x‖ +
      ‖∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ := by
      rw [halg]
      exact norm_sub_le _ _
    _ ≤ (‖((x + m : ℝ) : ℂ) * modFiveSmoothedPsi χ (x + m)‖ +
        ‖(x : ℂ) * modFiveSmoothedPsi χ x‖) + (m : ℝ) ^ 2 * Real.log (x + m) :=
      add_le_add (norm_sub_le _ _) (modFive_smoothed_remainder χ hx m)
    _ = _ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx,
        abs_of_pos (by positivity : 0 < x + (m : ℝ))]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronParameters
namespace OAI

/-! Elementary parameter choices for the smoothed Perron bound.  The
height is exp(y) and the original cutoff is exp(y²). -/

namespace TwoPointCorrelations

open _root_.Filter

lemma modFive_perron_height {y : ℝ} (hy : 2 ≤ y) :
    2 ≤ Real.exp y ∧ y ≤ Real.log (Real.exp y + 2) ∧
      Real.log (Real.exp y + 2) ≤ 2 * y := by
  have he : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  refine ⟨he, ?_, ?_⟩
  · simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos y) (by linarith : Real.exp y ≤ Real.exp y + 2)
  · have hh : Real.exp y + 2 ≤ Real.exp (2 * y) := by
      rw [show 2 * y = y + y by ring, Real.exp_add]
      nlinarith
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hh

lemma modFive_perron_right_power {y : ℝ} (hy : 0 < y) :
    (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) = Real.exp (y ^ 2 + 1) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp

lemma modFive_perron_left_power {a y H : ℝ} (ha : 0 ≤ a) (hy : 0 < y)
    (hH : 0 < H) (hHle : H ≤ 2 * y) :
    (Real.exp (y ^ 2)) ^ (1 - a / H) ≤ Real.exp (y ^ 2 - a * y / 2) := by
  have hq : y / 2 ≤ y ^ 2 / H := (le_div_iff₀ hH).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hq ha
  have he : a * (y ^ 2 / H) = y ^ 2 * (a / H) := by ring
  rw [he] at hm
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma modFive_perron_polynomial_absorption (K c : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, K * y ^ 2 * Real.exp (1 - c * y) ≤ 1 := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).const_mul
    (K * Real.exp 1)
  simp only [mul_zero] at ht
  have he : (fun y : ℝ => K * y ^ 2 * Real.exp (1 - c * y)) =
      (fun y : ℝ => (K * Real.exp 1) * (y ^ (2 : ℝ) * Real.exp (-c * y))) := by
    funext y
    rw [Real.rpow_two, show 1 - c * y = 1 + (-c * y) by ring, Real.exp_add]
    ring
  rw [← he] at ht
  exact (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedDecay
namespace OAI

/-! Exponential decay for the actual triangularly smoothed nonprincipal
Mangoldt sums, obtained by the explicit Perron height exp(sqrt(log x)). -/

namespace TwoPointCorrelations

open _root_.Filter

lemma modFive_contour_parameter_bound {a C D y : ℝ}
    (ha : 0 < a) (ha4 : a ≤ 1 / 4) (hC : 0 < C) (hD : 0 < D) (hy : 2 ≤ y) :
    4 * Real.pi * C * Real.log (Real.exp y + 2) ^ 2 *
        (Real.exp (y ^ 2)) ^ (1 - a / Real.log (Real.exp y + 2)) +
      4 * C * Real.log (Real.exp y + 2) ^ 2 *
        (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / (Real.exp y) ^ 2 +
      2 * (1 / (1 / y ^ 2) + D) *
        (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / Real.exp y ≤
      (16 * Real.pi * C + 16 * C + 2 * (1 + D)) * y ^ 2 *
        Real.exp (y ^ 2 + 1 - a * y / 2) := by
  have hyp : 0 < y := by linarith
  obtain ⟨_, hHlo, hHhi⟩ := modFive_perron_height hy
  have hHpos : 0 < Real.log (Real.exp y + 2) := hyp.trans_le hHlo
  have hHsq : Real.log (Real.exp y + 2) ^ 2 ≤ 4 * y ^ 2 := by
    convert (preTransparency := .instances) pow_le_pow_left₀ hHpos.le hHhi 2 using 1; ring
  have hleft := modFive_perron_left_power ha.le hyp hHpos hHhi
  have hright := modFive_perron_right_power hyp
  have hheight : (Real.exp y) ^ 2 = Real.exp (2 * y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  let F := Real.exp (y ^ 2 + 1 - a * y / 2)
  have hF : 0 ≤ F := (Real.exp_pos _).le
  have h1 : 4 * Real.pi * C * Real.log (Real.exp y + 2) ^ 2 *
      (Real.exp (y ^ 2)) ^ (1 - a / Real.log (Real.exp y + 2)) ≤
        (16 * Real.pi * C * y ^ 2) * F := by
    have hp : (Real.exp (y ^ 2)) ^ (1 - a / Real.log (Real.exp y + 2)) ≤ F :=
      hleft.trans (Real.exp_le_exp.mpr (by linarith))
    have hc : 4 * Real.pi * C * Real.log (Real.exp y + 2) ^ 2 ≤
        16 * Real.pi * C * y ^ 2 := by
      convert (preTransparency := .instances) mul_le_mul_of_nonneg_left hHsq
        (by positivity : 0 ≤ 4 * Real.pi * C) using 1; ring
    exact mul_le_mul hc hp (Real.rpow_nonneg (Real.exp_pos _).le _)
      (by positivity)
  have h2 : 4 * C * Real.log (Real.exp y + 2) ^ 2 *
      (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / (Real.exp y) ^ 2 ≤
        (16 * C * y ^ 2) * F := by
    have he : Real.exp (y ^ 2 + 1 - 2 * y) ≤ F := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [hright, hheight, mul_div_assoc, ← Real.exp_sub]
    have hc : 4 * C * Real.log (Real.exp y + 2) ^ 2 ≤ 16 * C * y ^ 2 := by
      convert (preTransparency := .instances) mul_le_mul_of_nonneg_left hHsq (by positivity : 0 ≤ 4 * C)
        using 1; ring
    exact mul_le_mul hc
      he (Real.exp_pos _).le (by positivity)
  have h3 : 2 * (1 / (1 / y ^ 2) + D) *
      (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / Real.exp y ≤
        (2 * (1 + D) * y ^ 2) * F := by
    have he : Real.exp (y ^ 2 + 1 - y) ≤ F := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [one_div_one_div, hright, mul_div_assoc, ← Real.exp_sub]
    have hysq : 1 ≤ y ^ 2 := by nlinarith
    have hc : 2 * (y ^ 2 + D) ≤ 2 * (1 + D) * y ^ 2 := by
      nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hysq)]
    exact mul_le_mul hc
      he (Real.exp_pos _).le (by positivity)
  exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by dsimp [F]; ring)

/-- Uniform over the three nonprincipal characters. -/
theorem modFive_smoothed_decay_exp_square : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ y : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 →
      (∀ n : ℕ, Real.exp (y ^ 2) ≠ (n : ℝ)) →
      ‖modFiveSmoothedPsi χ (Real.exp (y ^ 2))‖ ≤ Real.exp (y ^ 2 - c * y) := by
  obtain ⟨a, C, D, ha, ha4, hC, hD, hbound⟩ := modFive_smoothed_contour_bound
  let c := a / 4
  let K := 16 * Real.pi * C + 16 * C + 2 * (1 + D)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), modFive_perron_polynomial_absorption K c hc]
    with y hy hpoly χ hχ hxnat
  have hyp : 0 < y := by linarith
  have hδ : 0 < 1 / y ^ 2 := by positivity
  have hδ1 : 1 / y ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hx1 : 1 ≤ Real.exp (y ^ 2) := Real.one_le_exp (sq_nonneg y)
  have hmain := hbound χ hχ (Real.exp y) (Real.exp (y ^ 2)) (1 / y ^ 2)
    (modFive_perron_height hy).1 hx1 hδ hδ1 hxnat
  have hnum := modFive_contour_parameter_bound ha ha4 hC hD hy
  apply (hmain.trans hnum).trans
  have he : K * y ^ 2 * Real.exp (y ^ 2 + 1 - a * y / 2) =
      (K * y ^ 2 * Real.exp (1 - c * y)) * Real.exp (y ^ 2 - c * y) := by
    have hexp : y ^ 2 + 1 - a * y / 2 = (1 - c * y) + (y ^ 2 - c * y) := by
      dsimp [c]
      ring
    rw [hexp, Real.exp_add]
    ring
  change K * y ^ 2 * Real.exp (y ^ 2 + 1 - a * y / 2) ≤ _
  rw [he]
  exact (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le).trans_eq (one_mul _)

/-- The original real-cutoff form of the smoothed prime estimate. -/
theorem modFive_smoothed_decay : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 →
      (∀ n : ℕ, x ≠ (n : ℝ)) →
      ‖modFiveSmoothedPsi χ x‖ ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hbound⟩ := modFive_smoothed_decay_exp_square
  refine ⟨c, hc, ?_⟩
  have hcomp := (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually hbound
  filter_upwards [hcomp, eventually_ge_atTop (1 : ℝ)] with x hmain hx χ hχ hxnat
  dsimp only [Function.comp_def] at hmain
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hs : Real.sqrt (Real.log x) ^ 2 = Real.log x :=
    Real.sq_sqrt (Real.log_nonneg hx)
  have hb := hmain χ hχ (by simpa only [hs, Real.exp_log hxpos] using hxnat)
  simpa only [hs, Real.exp_log hxpos, sub_eq_add_neg, Real.exp_add,
    neg_mul] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveUnsmoothingScale
namespace OAI

/-! The finite-difference step with the actual short interval length.
A ceiling is used so that both triangular cutoffs have the same fractional
part, and the resulting exponential saving only loses a fixed factor. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma modFive_nonnat_add {x : ℝ} (hx : 0 ≤ x)
    (hxn : ∀ n : ℕ, x ≠ (n : ℝ)) (m : ℕ) :
    ∀ n : ℕ, x + m ≠ (n : ℝ) := by
  intro n he
  have hmn : m ≤ n := by exact_mod_cast (show (m : ℝ) ≤ n by linarith)
  apply hxn (n - m)
  rw [Nat.cast_sub hmn]
  linarith

lemma modFive_unsmoothing_numeric (χ : DirichletCharacter ℂ 5)
    {x c : ℝ} (hx : 1 ≤ x) (hc : 0 < c) {m : ℕ} (hm : 0 < m)
    (hmlow : x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤ m)
    (hmhigh : (m : ℝ) ≤ 2 * (x * Real.exp (-(c / 2) * Real.sqrt (Real.log x))))
    (hsx : ‖modFiveSmoothedPsi χ x‖ ≤ x * Real.exp (-c * Real.sqrt (Real.log x)))
    (hsy : ‖modFiveSmoothedPsi χ (x + m)‖ ≤
      (x + m) * Real.exp (-c * Real.sqrt (Real.log (x + m)))) :
    ‖modFiveTwistedPsi χ x‖ ≤
      x * (10 + 2 * Real.log (3 * x)) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
  let S := Real.sqrt (Real.log x)
  let E := Real.exp (-c * S)
  let e := Real.exp (-(c / 2) * S)
  let v := x * e
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have hep : 0 < e := Real.exp_pos _
  have hvp : 0 < v := mul_pos hxp hep
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith : -(c / 2) ≤ 0) hS)
  have hm2 : (m : ℝ) ≤ 2 * x := hmhigh.trans (by
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hxp.le he1) (by norm_num))
  have hy3 : x + (m : ℝ) ≤ 3 * x := by linarith
  have hyp : 0 < x + (m : ℝ) := by positivity
  have hlog : Real.log (x + m) ≤ Real.log (3 * x) :=
    Real.log_le_log hyp hy3
  have hlognonneg : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hSmono : S ≤ Real.sqrt (Real.log (x + m)) :=
    Real.sqrt_le_sqrt (Real.log_le_log hxp (le_add_of_nonneg_right (Nat.cast_nonneg m)))
  have hEmono : Real.exp (-c * Real.sqrt (Real.log (x + m))) ≤ E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hSmono (neg_nonpos.mpr hc.le)
  have hybound : ‖modFiveSmoothedPsi χ (x + m)‖ ≤ (x + m) * E :=
    hsy.trans (mul_le_mul_of_nonneg_left hEmono hyp.le)
  have hquad : (x + (m : ℝ)) ^ 2 ≤ 9 * x ^ 2 := by nlinarith
  have hnum : (x + m) * ‖modFiveSmoothedPsi χ (x + m)‖ +
      x * ‖modFiveSmoothedPsi χ x‖ ≤ 10 * x ^ 2 * E := by
    have hyb := mul_le_mul_of_nonneg_left hybound hyp.le
    have hxb := mul_le_mul_of_nonneg_left hsx hxp.le
    have hqb := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-c * S)).le
    change x * ‖modFiveSmoothedPsi χ x‖ ≤ x * (x * E) at hxb
    nlinarith
  have hupper := modFive_unsmoothing_bound χ hxp hm
  have hquot : 10 * x ^ 2 * E / (m : ℝ) ≤ 10 * x ^ 2 * E / v :=
    div_le_div_of_nonneg_left (by dsimp [E]; positivity) hvp hmlow
  have htail : (m : ℝ) * Real.log (x + m) ≤ 2 * v * Real.log (3 * x) := by
    calc
      _ ≤ (m : ℝ) * Real.log (3 * x) := mul_le_mul_of_nonneg_left hlog hmp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hmhigh hlognonneg
  have hEe : E = e ^ 2 := by
    dsimp [E, e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (10 * x ^ 2 * E + (m : ℝ) ^ 2 * Real.log (x + m)) / m :=
      hupper.trans (div_le_div_of_nonneg_right (add_le_add hnum le_rfl) hmp.le)
    _ = 10 * x ^ 2 * E / m + (m : ℝ) * Real.log (x + m) := by
      field_simp
    _ ≤ 10 * x ^ 2 * E / v + 2 * v * Real.log (3 * x) := add_le_add hquot htail
    _ = _ := by
      change 10 * x ^ 2 * E / v + 2 * v * Real.log (3 * x) =
        x * (10 + 2 * Real.log (3 * x)) * e
      rw [hEe]
      dsimp [v]
      field_simp

lemma modFive_unsmoothing_scale (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ∧
      (10 + 2 * Real.log (3 * x)) *
        Real.exp (-(c / 4) * Real.sqrt (Real.log x)) ≤ 1 := by
  have hp := modFive_perron_polynomial_absorption 16 (c / 4) (by positivity)
  have hs := (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually
    ((eventually_ge_atTop (max 1 (c / 2))).and hp)
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with x h hx
  let S := Real.sqrt (Real.log x)
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hS1 : 1 ≤ S := (le_max_left _ _).trans h.1
  have hSc : c / 2 ≤ S := (le_max_right _ _).trans h.1
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = Real.log x := Real.sq_sqrt (Real.log_nonneg hx)
  constructor
  · have he : x * Real.exp (-(c / 2) * S) = Real.exp (S ^ 2 - (c / 2) * S) := by
      rw [hSsq, sub_eq_add_neg, Real.exp_add, Real.exp_log hxp]
      congr 1
      ring_nf
    change 1 ≤ x * Real.exp (-(c / 2) * S)
    rw [he]
    apply Real.one_le_exp
    nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hSc)]
  · have hlog3 : Real.log 3 ≤ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hcoef : 10 + 2 * Real.log (3 * x) ≤ 16 * S ^ 2 := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hxp.ne']
      nlinarith [sq_nonneg (S - 1)]
    have he : Real.exp (-(c / 4) * S) ≤ Real.exp (1 - (c / 4) * S) :=
      Real.exp_le_exp.mpr (by linarith)
    exact (mul_le_mul hcoef he (Real.exp_pos _).le (by positivity)).trans h.2

/-- The nonprincipal twisted Mangoldt sum has a quantitative exponential
saving. Nonintegral cutoffs suffice here and are removed by floor transfer. -/
theorem modFive_unsmoothed_decay_nonnat : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 →
      (∀ n : ℕ, x ≠ (n : ℝ)) →
      ‖modFiveTwistedPsi χ x‖ ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hs⟩ := modFive_smoothed_decay
  obtain ⟨X, hX⟩ := eventually_atTop.mp hs
  refine ⟨c / 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop X, eventually_ge_atTop (1 : ℝ),
    modFive_unsmoothing_scale c hc] with x hxX hx hscale χ hχ hxnat
  let S := Real.sqrt (Real.log x)
  let v := x * Real.exp (-(c / 2) * S)
  let m := ⌈v⌉₊
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hv1 : 1 ≤ v := hscale.1
  have hvp : 0 < v := zero_lt_one.trans_le hv1
  have hmlo : v ≤ (m : ℝ) := Nat.le_ceil v
  have hm : 0 < m := by
    have hmp : 0 < (m : ℝ) := hvp.trans_le hmlo
    exact_mod_cast hmp
  have hmhi : (m : ℝ) ≤ 2 * v := by
    have hh : (m : ℝ) < v + 1 := Nat.ceil_lt_add_one hvp.le
    linarith
  have hys : X ≤ x + (m : ℝ) :=
    hxX.trans (le_add_of_nonneg_right (Nat.cast_nonneg m))
  have hnum := modFive_unsmoothing_numeric χ hx hc hm hmlo hmhi
    (hX x hxX χ hχ hxnat)
    (hX (x + m) hys χ hχ (modFive_nonnat_add (by linarith) hxnat m))
  have he : x * (10 + 2 * Real.log (3 * x)) * Real.exp (-(c / 2) * S) =
      (x * Real.exp (-(c / 4) * S)) *
        ((10 + 2 * Real.log (3 * x)) * Real.exp (-(c / 4) * S)) := by
    have harg : -(c / 2) * S = -(c / 4) * S + -(c / 4) * S := by ring
    rw [harg, Real.exp_add]
    ring
  apply hnum.trans
  change x * (10 + 2 * Real.log (3 * x)) * Real.exp (-(c / 2) * S) ≤ _
  rw [he]
  exact (mul_le_mul_of_nonneg_left hscale.2 (by positivity)).trans_eq (mul_one _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePsiDecay
namespace OAI

/-! Removal of the nonintegral-cutoff condition.  The Mangoldt sums only
depend on the floor; the midpoint of the same unit interval is always an
admissible triangular cutoff. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma modFive_half_cutoff_nonnat (N : ℕ) :
    ∀ n : ℕ, (N : ℝ) + 1 / 2 ≠ (n : ℝ) := by
  intro n he
  have hh : (2 : ℝ) * (N : ℝ) + 1 = 2 * (n : ℝ) := by linarith
  have hn : 2 * N + 1 = 2 * n := by exact_mod_cast hh
  omega

lemma modFive_half_cutoff_floor (N : ℕ) :
    ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor <;> linarith

lemma modFive_half_cutoff_geometry {x : ℝ} (hx : 4 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) + 1 / 2 ∧
    (⌊x⌋₊ : ℝ) + 1 / 2 ≤ 2 * x ∧
    Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log ((⌊x⌋₊ : ℝ) + 1 / 2)) := by
  have hxp : 0 < x := by linarith
  have hfloor := Nat.floor_le hxp.le
  have hfloorlt := Nat.lt_floor_add_one x
  have htlow : x / 2 ≤ (⌊x⌋₊ : ℝ) + 1 / 2 := by linarith
  have hthi : (⌊x⌋₊ : ℝ) + 1 / 2 ≤ 2 * x := by linarith
  refine ⟨htlow, hthi, ?_⟩
  have htp : 0 < (⌊x⌋₊ : ℝ) + 1 / 2 := by positivity
  have hlogx : 2 * Real.log 2 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith
  have hlogt : Real.log x - Real.log 2 ≤ Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < x / 2) htlow
    rwa [Real.log_div hxp.ne' (by norm_num)] at hh
  have hlogtnonneg : 0 ≤ Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) :=
    Real.log_nonneg (by linarith)
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hlogtnonneg, div_pow, Real.sq_sqrt (Real.log_nonneg (by linarith))]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  norm_num
  linarith

/-- The full real-cutoff estimate for every nonprincipal character mod 5. -/
theorem modFive_nonprincipal_psi_decay : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 →
      ‖modFiveTwistedPsi χ x‖ ≤ 2 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hbound⟩ := modFive_unsmoothed_decay_nonnat
  obtain ⟨X, hX⟩ := eventually_atTop.mp hbound
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 (2 * X))] with x hx χ hχ
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  obtain ⟨htlow, hthi, hroot⟩ := modFive_half_cutoff_geometry hx4
  let t := (⌊x⌋₊ : ℝ) + 1 / 2
  have htX : X ≤ t := by
    have hlarge : 2 * X ≤ x := (le_max_right _ _).trans hx
    dsimp [t]
    linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hsum : modFiveTwistedPsi χ t = modFiveTwistedPsi χ x := by
    simp only [modFiveTwistedPsi, t, modFive_half_cutoff_floor]
  have hm := hX t htX χ hχ (modFive_half_cutoff_nonnat ⌊x⌋₊)
  rw [hsum] at hm
  have he : Real.exp (-c * Real.sqrt (Real.log t)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_left hroot (neg_nonpos.mpr hc.le)
    dsimp [t] at *
    nlinarith
  exact hm.trans (mul_le_mul hthi he (Real.exp_pos _).le (by linarith))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrincipalPsi
namespace OAI

/-! The principal character only removes powers of five.  For the required
error bound it is enough to charge the prime 5 once, and all remaining
terms to the already proved elementary prime-power error. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩

lemma modFive_principal_term_bound (n : ℕ) :
    ‖modFiveMangoldtTwist 1 n - (vonMangoldt n : ℂ)‖ ≤
      (if n = 5 then Real.log 5 else 0) +
        (vonMangoldt n - if n.Prime then Real.log n else 0) := by
  by_cases hp : n.Prime
  · by_cases hn : n = 5
    · subst n
      have hz : (1 : DirichletCharacter ℂ 5) (5 : ZMod 5) = 0 := by
        rw [show (5 : ZMod 5) = 0 by decide, MulChar.map_zero]
      rw [modFiveMangoldtTwist]
      simp only [Nat.cast_ofNat]
      rw [hz, zero_mul, zero_sub, norm_neg, vonMangoldt_apply_prime hp]
      simp only [hp, ↓reduceIte, Nat.cast_ofNat, sub_self, add_zero]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5))]
    · have hcop : n.Coprime 5 := hp.coprime_iff_not_dvd.mpr (by
        intro hd
        exact hn ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hd))
      have hu : IsUnit (n : ZMod 5) := (ZMod.isUnit_iff_coprime n 5).mpr hcop
      have hone : (1 : DirichletCharacter ℂ 5) (n : ZMod 5) = 1 := MulChar.one_apply hu
      simp [modFiveMangoldtTwist, hone, hp, hn, vonMangoldt_apply_prime hp]
  · have hn : n ≠ 5 := by intro he; subst n; exact hp (by decide)
    by_cases hu : IsUnit (n : ZMod 5)
    · have hone : (1 : DirichletCharacter ℂ 5) (n : ZMod 5) = 1 := MulChar.one_apply hu
      simp [modFiveMangoldtTwist, hone, hp, hn, vonMangoldt_nonneg]
    · have hzero : (1 : DirichletCharacter ℂ 5) (n : ZMod 5) = 0 := MulChar.map_nonunit _ hu
      simp [modFiveMangoldtTwist, hzero, hp, hn, abs_of_nonneg vonMangoldt_nonneg]

lemma modFive_principal_psi_error {x : ℝ} (hx : 1 ≤ x) :
    ‖modFiveTwistedPsi 1 x - (Chebyshev.psi x : ℂ)‖ ≤
      Real.log 5 + 2 * Real.sqrt x * Real.log x := by
  have hid : modFiveTwistedPsi 1 x - (Chebyshev.psi x : ℂ) =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (modFiveMangoldtTwist 1 n - (vonMangoldt n : ℂ)) := by
    rw [modFiveTwistedPsi_eq, Chebyshev.psi_eq_sum_Icc, Complex.ofReal_sum,
      sum_sub_distrib]
  have hfive : (∑ n ∈ Icc 0 ⌊x⌋₊, if n = 5 then Real.log 5 else 0) ≤ Real.log 5 := by
    by_cases h5 : 5 ∈ Icc 0 ⌊x⌋₊
    · simp [h5]
    · simp [h5, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)]
  have hrem : (∑ n ∈ Icc 0 ⌊x⌋₊,
      (vonMangoldt n - if n.Prime then Real.log n else 0)) =
      Chebyshev.psi x - Chebyshev.theta x := by
    rw [sum_sub_distrib, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, sum_filter]
  rw [hid]
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊x⌋₊, ‖modFiveMangoldtTwist 1 n - (vonMangoldt n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 0 ⌊x⌋₊,
        ((if n = 5 then Real.log 5 else 0) +
          (vonMangoldt n - if n.Prime then Real.log n else 0)) :=
      sum_le_sum fun n _ => modFive_principal_term_bound n
    _ = (∑ n ∈ Icc 0 ⌊x⌋₊, if n = 5 then Real.log 5 else 0) +
        (Chebyshev.psi x - Chebyshev.theta x) := by rw [sum_add_distrib, hrem]
    _ ≤ _ := add_le_add hfive (Chebyshev.psi_sub_theta_le hx)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveZetaPsi
namespace OAI

/-! The principal twisted Mangoldt estimate from the already proved zeta
prime number theorem, with the elementary five-power correction retained. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma modFive_constant_absorption (c : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ Real.exp (c ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hsq := Real.sq_sqrt (Real.log_nonneg hx)
  have hn : 0 ≤ c ^ 2 + Real.log x - c * Real.sqrt (Real.log x) := by
    nlinarith [sq_nonneg (Real.sqrt (Real.log x) - c / 2), sq_nonneg c]
  have he : Real.exp (c ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) =
      Real.exp (c ^ 2 + Real.log x - c * Real.sqrt (Real.log x)) := by
    calc
      _ = Real.exp (c ^ 2) * Real.exp (Real.log x) *
          Real.exp (-c * Real.sqrt (Real.log x)) := by rw [Real.exp_log hxp]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [he]
  exact Real.one_le_exp hn


theorem modFive_principal_psi_decay : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ‖modFiveTwistedPsi 1 x - (x : ℂ)‖ ≤
      C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := modFive_zeta_psi_decay
  let K := C + (Real.log 5 + 8) * Real.exp (c ^ 2)
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  refine ⟨c, K, hc, by dsimp [K]; positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hb hx
  have herr := modFive_principal_psi_error hx
  have hp := sqrt_mul_log_le_exp_sqrt c hx
  have hone := mul_le_mul_of_nonneg_left (modFive_constant_absorption c hx) hlog5
  have hcast : ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ = |Chebyshev.psi x - x| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ = ‖(modFiveTwistedPsi 1 x - (Chebyshev.psi x : ℂ)) +
        ((Chebyshev.psi x : ℂ) - (x : ℂ))‖ := by congr 1; ring
    _ ≤ ‖modFiveTwistedPsi 1 x - (Chebyshev.psi x : ℂ)‖ +
        ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ := norm_add_le _ _
    _ ≤ (Real.log 5 + 2 * Real.sqrt x * Real.log x) +
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      rw [hcast]
      exact add_le_add herr hb
    _ ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      dsimp [K]
      nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
namespace OAI

/-! The fixed modulus-five prime number theorem follows from the three
nonprincipal contour estimates, the zeta prime number theorem, and finite
character orthogonality. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩

lemma modFive_character_card : Fintype.card (DirichletCharacter ℂ 5) = 4 := by
  have hh := modFive_character_sum 1
  simp only [Nat.cast_one, map_one, sum_const, card_univ, nsmul_eq_mul, mul_one,
    show 1 % 5 = 1 by decide, ↓reduceIte] at hh
  exact_mod_cast hh

lemma modFive_rate_mono {a b x : ℝ} (hab : a ≤ b) :
    Real.exp (-b * Real.sqrt (Real.log x)) ≤ Real.exp (-a * Real.sqrt (Real.log x)) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hab) (Real.sqrt_nonneg _)

theorem modFive_all_character_error : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5,
      ‖modFiveTwistedPsi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨a, ha, hnp⟩ := modFive_nonprincipal_psi_decay
  obtain ⟨b, B, hb, hB, hpr⟩ := modFive_principal_psi_decay
  refine ⟨min a b, B + 2, lt_min ha hb, by positivity, ?_⟩
  filter_upwards [hnp, hpr, eventually_ge_atTop (1 : ℝ)] with x hnp hpr hx χ
  by_cases hχ : χ = 1
  · subst χ
    rw [if_pos rfl]
    calc
      _ ≤ B * x * Real.exp (-b * Real.sqrt (Real.log x)) := hpr
      _ ≤ (B + 2) * x * Real.exp (-(min a b) * Real.sqrt (Real.log x)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by linarith : B ≤ B + 2) (by linarith)
        · exact modFive_rate_mono (min_le_right _ _)
        · exact (Real.exp_pos _).le
        · positivity
  · rw [if_neg hχ, sub_zero]
    calc
      _ ≤ 2 * x * Real.exp (-a * Real.sqrt (Real.log x)) := hnp χ hχ
      _ ≤ (B + 2) * x * Real.exp (-(min a b) * Real.sqrt (Real.log x)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by linarith : 2 ≤ B + 2) (by linarith)
        · exact modFive_rate_mono (min_le_left _ _)
        · exact (Real.exp_pos _).le
        · positivity

lemma modFive_selected_psi_error {x E : ℝ}
    (h : ∀ χ : DirichletCharacter ℂ 5,
      ‖modFiveTwistedPsi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ E) :
    |modFivePsi true x - x / 4| ≤ E := by
  have he : (4 : ℂ) * ((modFivePsi true x - x / 4 : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ 5,
        (modFiveTwistedPsi χ x - (if χ = 1 then (x : ℂ) else 0)) := by
    rw [sum_sub_distrib]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
    rw [← modFivePsi_true_character_sum]
    push_cast
    ring
  have hn : 4 * |modFivePsi true x - x / 4| ≤ 4 * E := by
    calc
      _ = ‖(4 : ℂ) * ((modFivePsi true x - x / 4 : ℝ) : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ ∑ χ : DirichletCharacter ℂ 5,
          ‖modFiveTwistedPsi χ x - (if χ = 1 then (x : ℂ) else 0)‖ := by
        rw [he]
        exact norm_sum_le _ _
      _ ≤ ∑ _χ : DirichletCharacter ℂ 5, E := sum_le_sum fun χ _ => h χ
      _ = _ := by simp [modFive_character_card]
  linarith

theorem modFive_eventual_psi : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ᶠ x : ℝ in atTop, ∀ one : Bool,
      |modFivePsi one x - modFiveDensity one * x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨a, A, ha, hA, hchars⟩ := modFive_all_character_error
  obtain ⟨b, B, hb, hB, hzeta⟩ := modFive_zeta_psi_decay
  refine ⟨min a b, A + B, lt_min ha hb, by positivity, ?_⟩
  filter_upwards [hchars, hzeta, eventually_ge_atTop (1 : ℝ)] with x hchars hzeta hx one
  have htrue : |modFivePsi true x - (1 / 4) * x| ≤
      A * x * Real.exp (-(min a b) * Real.sqrt (Real.log x)) := by
    have hh := modFive_selected_psi_error hchars
    have he : x / 4 = (1 / 4 : ℝ) * x := by ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (modFive_rate_mono (min_le_left _ _))
      (by positivity))
  have hz : |Chebyshev.psi x - x| ≤
      B * x * Real.exp (-(min a b) * Real.sqrt (Real.log x)) :=
    hzeta.trans (mul_le_mul_of_nonneg_left (modFive_rate_mono (min_le_right _ _))
      (by positivity))
  cases one
  · have he : modFivePsi false x - (3 / 4) * x =
        (Chebyshev.psi x - x) - (modFivePsi true x - (1 / 4) * x) := by
      linear_combination modFivePsi_complement x
    change |modFivePsi false x - (3 / 4) * x| ≤ _
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add hz htrue).trans_eq (by ring))
  · change |modFivePsi true x - (1 / 4) * x| ≤ _
    exact htrue.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ A + B) (by linarith))
      (Real.exp_pos _).le)

/-- The logarithmically weighted prime estimate in the two selected
modulus-five classes, obtained by contour integration and orthogonality. -/
theorem modFiveThetaInput_oai : ModFiveThetaInput := by
  obtain ⟨c, C, hc, hC, h⟩ := modFive_eventual_psi
  exact modFiveThetaInput_of_eventual_psi c C hc hC h

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.modFiveThetaInput_oai := @OAI.TwoPointCorrelations.modFiveThetaInput_oai
