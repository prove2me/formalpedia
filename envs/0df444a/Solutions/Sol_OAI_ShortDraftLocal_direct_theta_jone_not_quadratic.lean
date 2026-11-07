-- Prove2me | solution 1 for OAI.ShortDraftLocal.direct_theta_jone_not_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:44:17.993223+00:00
-- url     : https://prove2.me/submissions/ca4305ad-bb13-4250-918c-656e6bb188fe

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows

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
open OAI.ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F] [DecidableEq F]
namespace OAI.ShortDraftLocal
theorem _root_.solution (χ : MulChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) : χ ≠ χ ^ 3 := by
  intro h
  apply hχ₂
  calc
    χ ^ 2 = χ ^ 3 * χ⁻¹ := by group
    _ = χ * χ⁻¹ := by rw [← h]
    _ = 1 := by group
end OAI.ShortDraftLocal
