-- Prove2me | solution 1 for GlobalTheory.T.hecke_algebra_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:28.881449+00:00
-- url     : https://prove2.me/submissions/fcad61ae-34c3-4bd3-ae36-35fe040dde88

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeAlgebraStructure
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeAlgebraStructureStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAlg_hk_alg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | exact GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | (intros; apply GlobalTheory.CompanionTheory.HeckeAlg.hk_alg <;> assumption)
end _root_.GlobalTheory.T
