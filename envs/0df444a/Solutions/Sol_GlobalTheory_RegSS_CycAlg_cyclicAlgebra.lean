-- Prove2me | solution 1 for GlobalTheory.RegSS.CycAlg.cyclicAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:45:35.285136+00:00
-- url     : https://prove2.me/submissions/93da6c58-db3a-4836-bdf8-ffbf06f33f6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_actOn_bijective
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_toGen_mk
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_toGen_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.CycAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS.CycAlg
theorem _root_.solution : GlobalTheory.RegSS.CyclicAlgebra := by
  intro A _ n _ _ M v h
  refine ⟨⟨AlgEquiv.ofBijective (toGen M) (toGen_bijective h), ?_⟩,
    ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective (actOn M v) (actOn_bijective h))⟩,
    actOn_bijective h⟩
  change toGen M (AdjoinRoot.mk _ X) = _
  rw [toGen_mk, aeval_X]
end GlobalTheory.RegSS.CycAlg
