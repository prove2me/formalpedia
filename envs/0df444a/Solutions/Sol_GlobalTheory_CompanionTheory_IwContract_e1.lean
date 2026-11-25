-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:42.578644+00:00
-- url     : https://prove2.me/submissions/9b5da16e-d352-4234-8a7a-1c1274d86a64

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_contraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.IwContract
theorem _root_.solution : PositivityTheory.Rg.Tf.Loc.E1 := by
  intro F _ _ _ _ n ϖ hϖ a ha γ hγ
  exact contraction hϖ ha γ hγ
end GlobalTheory.CompanionTheory.IwContract
