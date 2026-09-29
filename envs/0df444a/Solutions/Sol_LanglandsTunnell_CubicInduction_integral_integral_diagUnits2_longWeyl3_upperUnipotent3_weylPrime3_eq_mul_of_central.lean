-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3731960f-2d9a-5a06-8aca-9ad122459747

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Matrix

noncomputable section

namespace LTMiddleIdentity

open LanglandsTunnell.CubicInduction

section Algebra

variable {F : Type*} [Field F]

theorem point_eq (t a u : Fˣ) :
    iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 (u : F) * weylPrime3) =
      upperUnipotent3 0 0 ((t : F) * a * ((u⁻¹ : Fˣ) : F)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 3) u *
          (iotaGL (diagUnits2 (-(t * u⁻¹) * (a * u⁻¹)) (a * u⁻¹)) *
            (longWeyl3 * upperUnipotent3 0 0 ((u⁻¹ : Fˣ) : F) * longWeyl3 * weylPrime3))) := by
  refine Units.ext ?_
  simp only [Units.val_mul, longWeyl3_coe, weylPrime3_coe, upperUnipotent3_coe, coe_iotaGL, coe_diagUnits2,
    Units.val_neg, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, embedMat2]
  all_goals field_simp
  all_goals ring

end Algebra

section Weights

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

def mC (x : Kˣ) : ℂ := ((modulus (x : K) : ℝ) : ℂ)

theorem mC_def (x : Kˣ) : mC x = ((modulus (x : K) : ℝ) : ℂ) := rfl

theorem mC_eq (x : Kˣ) : mC x = ((distribHaarChar K x : ℝ) : ℂ) := by
  rw [mC_def, modulus_coe_units]

theorem mC_mul (x y : Kˣ) : mC (x * y) = mC x * mC y := by
  rw [mC_eq, mC_eq, mC_eq, map_mul, NNReal.coe_mul, Complex.ofReal_mul]

theorem distribHaarChar_neg_one : distribHaarChar K (-1 : Kˣ) = 1 := by
  have h : distribHaarChar K (-1 : Kˣ) * distribHaarChar K (-1 : Kˣ) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have h' : ((distribHaarChar K (-1 : Kˣ) : ℝ)) * (distribHaarChar K (-1 : Kˣ) : ℝ) = 1 := by
    exact_mod_cast h
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · exact_mod_cast h1
  · exfalso
    have : (0 : ℝ) ≤ (distribHaarChar K (-1 : Kˣ) : ℝ) := NNReal.coe_nonneg _
    linarith

theorem mC_neg (x : Kˣ) : mC (-x) = mC x := by
  rw [mC_eq, mC_eq, show (-x : Kˣ) = -1 * x by rw [neg_one_mul], map_mul, distribHaarChar_neg_one, one_mul]

theorem mC_pos (x : Kˣ) : (0 : ℝ) < (modulus (x : K) : ℝ) := by
  exact_mod_cast modulus_pos x.ne_zero

theorem mC_nonneg (x : Kˣ) : (0 : ℝ) ≤ (modulus (x : K) : ℝ) := (mC_pos x).le

theorem mC_ne_zero (x : Kˣ) : mC x ≠ 0 := by
  rw [mC_def]
  exact_mod_cast (mC_pos x).ne'

theorem mC_mul_cpow (x y : Kˣ) (r : ℂ) : mC (x * y) ^ r = mC x ^ r * mC y ^ r := by
  rw [mC_mul, mC_def, mC_def, Complex.mul_cpow_ofReal_nonneg (mC_nonneg x) (mC_nonneg y)]

theorem mC_cpow_mul_cpow_neg (x : Kˣ) (s : ℂ) : mC x ^ s * mC x ^ (-s - 1) = (mC x)⁻¹ := by
  rw [← Complex.cpow_add _ _ (mC_ne_zero x), show s + (-s - 1) = (-1 : ℂ) by ring, Complex.cpow_neg_one]

def chC (χ : Kˣ →* ℂˣ) (x : Kˣ) : ℂ := ((χ x : ℂˣ) : ℂ)

theorem chC_def (χ : Kˣ →* ℂˣ) (x : Kˣ) : chC χ x = ((χ x : ℂˣ) : ℂ) := rfl

theorem chC_mul (χ : Kˣ →* ℂˣ) (x y : Kˣ) : chC χ (x * y) = chC χ x * chC χ y := by
  rw [chC_def, chC_def, chC_def, map_mul, Units.val_mul]

theorem chC_neg (χ : Kˣ →* ℂˣ) (x : Kˣ) : chC χ (-x) = chC χ (-1) * chC χ x := by
  rw [show (-x : Kˣ) = -1 * x by rw [neg_one_mul], chC_mul]

theorem chC_ne_zero (χ : Kˣ →* ℂˣ) (x : Kˣ) : chC χ x ≠ 0 := Units.ne_zero _

def wt (ω χ₀ χ₁ : Kˣ →* ℂˣ) (s : ℂ) (a t : Kˣ) : ℂ :=
  (chC χ₁ a)⁻¹ * (chC ω a)⁻¹ * mC a ^ s * (chC χ₀ t * mC t ^ (-s - 1))

theorem wt_def (ω χ₀ χ₁ : Kˣ →* ℂˣ) (s : ℂ) (a t : Kˣ) :
    wt ω χ₀ χ₁ s a t = (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
      (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) := rfl

theorem wt_subst (ω χ₀ χ₁ : Kˣ →* ℂˣ) (s : ℂ) (u a t : Kˣ) :
    wt ω χ₀ χ₁ s (u * a) (-u * t) * chC ω u =
      (chC χ₀ (-1) * chC χ₀ u * (chC χ₁ u)⁻¹ * (mC u)⁻¹) * wt ω χ₀ χ₁ s a t := by
  have hneg : (-u * t : Kˣ) = -(u * t) := by rw [neg_mul]
  rw [wt, wt, hneg, chC_mul χ₁, chC_mul ω, chC_neg χ₀, chC_mul χ₀, mC_neg, mC_mul_cpow, mC_mul_cpow]
  have hω : (chC ω u)⁻¹ * chC ω u = 1 := inv_mul_cancel₀ (chC_ne_zero ω u)
  have hm : mC u ^ s * mC u ^ (-s - 1) = (mC u)⁻¹ := mC_cpow_mul_cpow_neg u s
  calc (chC χ₁ u * chC χ₁ a)⁻¹ * (chC ω u * chC ω a)⁻¹ * (mC u ^ s * mC a ^ s) *
        (chC χ₀ (-1) * (chC χ₀ u * chC χ₀ t) * (mC u ^ (-s - 1) * mC t ^ (-s - 1))) * chC ω u
      = (chC χ₀ (-1) * chC χ₀ u * (chC χ₁ u)⁻¹ * ((chC ω u)⁻¹ * chC ω u) * (mC u ^ s * mC u ^ (-s - 1))) *
          ((chC χ₁ a)⁻¹ * (chC ω a)⁻¹ * mC a ^ s * (chC χ₀ t * mC t ^ (-s - 1))) := by
        rw [mul_inv, mul_inv]
        ring
    _ = (chC χ₀ (-1) * chC χ₀ u * (chC χ₁ u)⁻¹ * (mC u)⁻¹) *
          ((chC χ₁ a)⁻¹ * (chC ω a)⁻¹ * mC a ^ s * (chC χ₀ t * mC t ^ (-s - 1))) := by
        rw [hω, hm, mul_one]

end Weights

end LTMiddleIdentity

open LanglandsTunnell.CubicInduction LTMiddleIdentity

theorem solution
    {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    [MeasurableSpace Kˣ] [MeasurableMul Kˣ] (μ : Measure Kˣ) [μ.IsMulLeftInvariant]
    (ψ : AddChar K ℂ) (W : GL (Fin 3) K → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : Kˣ →* ℂˣ)
    (hω : ∀ (z : Kˣ) (g : GL (Fin 3) K), W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (χ₀ χ₁ : Kˣ →* ℂˣ) (s : ℂ) (u : Kˣ) :
    (∫ a : Kˣ, ∫ t : Kˣ,
        (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
          (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) *
        W (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 (u : K) * weylPrime3)) ∂μ ∂μ) =
      ((χ₀ (-1) : ℂˣ) : ℂ) * ((χ₀ u : ℂˣ) : ℂ) * ((χ₁ u : ℂˣ) : ℂ)⁻¹ * (((modulus (u : K) : ℝ) : ℂ))⁻¹ *
      ∫ a : Kˣ, ∫ t : Kˣ,
        (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
          (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) *
        W (iotaGL (diagUnits2 (t * a) a) *
          (longWeyl3 * upperUnipotent3 0 0 ((u⁻¹ : Kˣ) : K) * longWeyl3 * weylPrime3)) ∂μ ∂μ := by

  set M : GL (Fin 3) K := longWeyl3 * upperUnipotent3 0 0 ((u⁻¹ : Kˣ) : K) * longWeyl3 * weylPrime3 with hM
  set P : Kˣ → Kˣ → GL (Fin 3) K := fun t a => iotaGL (diagUnits2 (t * a) a) * M with hP
  set κ : ℂ := chC χ₀ (-1) * chC χ₀ u * (chC χ₁ u)⁻¹ * (mC u)⁻¹ with hκ

  have hpt : ∀ a t : Kˣ,
      (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
          (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) *
        W (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 (u : K) * weylPrime3)) =
      wt ω χ₀ χ₁ s a t * (chC ω u * W (P (-(t * u⁻¹)) (a * u⁻¹))) := by
    intro a t
    rw [point_eq, hW, zero_add, AddChar.map_zero_eq_one, one_mul, hω, wt_def, chC_def]

  have hsub : (∫ a : Kˣ, ∫ t : Kˣ, wt ω χ₀ χ₁ s a t * (chC ω u * W (P (-(t * u⁻¹)) (a * u⁻¹))) ∂μ ∂μ) =
      ∫ a : Kˣ, ∫ t : Kˣ, wt ω χ₀ χ₁ s (u * a) (-u * t) * (chC ω u * W (P t a)) ∂μ ∂μ := by
    have hin : ∀ a : Kˣ, (∫ t : Kˣ, wt ω χ₀ χ₁ s a t * (chC ω u * W (P (-(t * u⁻¹)) (a * u⁻¹))) ∂μ) =
        ∫ t : Kˣ, wt ω χ₀ χ₁ s a (-u * t) * (chC ω u * W (P t (a * u⁻¹))) ∂μ := by
      intro a
      rw [← integral_mul_left_eq_self
        (fun t => wt ω χ₀ χ₁ s a t * (chC ω u * W (P (-(t * u⁻¹)) (a * u⁻¹)))) (-u)]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      have : -(-u * t * u⁻¹) = t := by
        rw [neg_mul, neg_mul, neg_neg, mul_comm u t, mul_assoc, mul_inv_cancel, mul_one]
      simp only [this]
    simp_rw [hin]
    rw [← integral_mul_left_eq_self
      (fun a => ∫ t : Kˣ, wt ω χ₀ χ₁ s a (-u * t) * (chC ω u * W (P t (a * u⁻¹))) ∂μ) u]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    have : u * a * u⁻¹ = a := by rw [mul_comm u a, mul_assoc, mul_inv_cancel, mul_one]
    simp only [this]

  have hwt : ∀ a t : Kˣ, wt ω χ₀ χ₁ s (u * a) (-u * t) * (chC ω u * W (P t a)) = κ * (wt ω χ₀ χ₁ s a t * W (P t a)) := by
    intro a t
    rw [← mul_assoc, wt_subst, hκ]
    ring
  calc (∫ a : Kˣ, ∫ t : Kˣ,
        (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
          (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) *
        W (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 (u : K) * weylPrime3)) ∂μ ∂μ)
      = ∫ a : Kˣ, ∫ t : Kˣ, wt ω χ₀ χ₁ s a t * (chC ω u * W (P (-(t * u⁻¹)) (a * u⁻¹))) ∂μ ∂μ := by
        simp only [hpt]
    _ = ∫ a : Kˣ, ∫ t : Kˣ, wt ω χ₀ χ₁ s (u * a) (-u * t) * (chC ω u * W (P t a)) ∂μ ∂μ := hsub
    _ = ∫ a : Kˣ, ∫ t : Kˣ, κ * (wt ω χ₀ χ₁ s a t * W (P t a)) ∂μ ∂μ := by simp only [hwt]
    _ = κ * ∫ a : Kˣ, ∫ t : Kˣ, wt ω χ₀ χ₁ s a t * W (P t a) ∂μ ∂μ := by
        simp_rw [integral_const_mul]
    _ = _ := by
        rw [hκ, chC_def, chC_def, chC_def, mC_def]
        rfl

end
end S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central (solution)
