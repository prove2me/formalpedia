-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberExpSum_inv_locallyIntegrableOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:14.62278+00:00
-- url     : https://prove2.me/submissions/314a1c36-a7fc-43d9-ada3-6aecf350cd8f

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_continuousOn_pos

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
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0) :
    LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0) := by
  have hcont : ContinuousOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0) := by
    apply (normFiberExpSum_continuousOn_pos χ ψ weight hcoeff ha0).comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    exact inv_pos.mpr (show 0 < D from hD)
  exact hcont.locallyIntegrableOn measurableSet_Ioi
end OAI.ShortDraftHeckeBridge
