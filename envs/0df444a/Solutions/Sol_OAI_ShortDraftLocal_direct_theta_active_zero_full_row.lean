-- Prove2me | solution 1 for OAI.ShortDraftLocal.direct_theta_active_zero_full_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:49:16.401839+00:00
-- url     : https://prove2.me/submissions/bb41e879-5567-4ad5-a21d-008640daf585

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ShortDraftLocal_direct_theta_active_zero_fourier_row
import Theorems.Thm_OAI_ShortDraftLocal_trivial_fourier_coefficient


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open OAI.ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
namespace OAI.ShortDraftLocal
theorem _root_.solution (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hχ₂ : χ ^ 2 ≠ 1) (hψ : ψ ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 0) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 0) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h _
    rw [pow_zero, trivial_fourier_coefficient ψ hψ h,
      if_neg (Units.ne_zero h)]
    ring
  rw [hsum]
  convert direct_theta_active_zero_fourier_row χ ψ hχ₂ σ ε x using 1 ; ring
end OAI.ShortDraftLocal
