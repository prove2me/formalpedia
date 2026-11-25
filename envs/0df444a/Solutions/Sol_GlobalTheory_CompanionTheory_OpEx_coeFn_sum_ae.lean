-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OpEx.coeFn_sum_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:41.972805+00:00
-- url     : https://prove2.me/submissions/5845cdb6-8b2e-4b95-ad73-7ef7acabb9e4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTailRest
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoeFnSumAe
import Theorems.Thm_UpperTheory_Reformulated_B_Yxa1_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OpEx
open PositivityTheory.Rg.BcB.E1
namespace GlobalTheory.CompanionTheory.OpEx
theorem _root_.solution {α : Type} [MeasurableSpace α] {ν : Measure α} {ι : Type} (s : Finset ι)
    (g : ι → Lp ℂ 2 ν) :
    ((∑ j ∈ s, g j : Lp ℂ 2 ν) : α → ℂ) =ᵐ[ν] fun x => ∑ j ∈ s, (g j : α → ℂ) x :=
  _root_.UpperTheory.Reformulated.B.Yxa1.main s g
end GlobalTheory.CompanionTheory.OpEx
