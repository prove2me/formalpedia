-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.val_entry_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:36.356015+00:00
-- url     : https://prove2.me/submissions/e1925670-d75f-4581-a8df-e87f0c188936

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction

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
theorem _root_.solution {g : GL (Fin n) F} (hg : g ∈ GlobalTheory.SmGL.iwahori F (Fin n)) (i j : Fin n) :
    valuation F (g.val i j) ≤ 1 := by
  obtain ⟨⟨h, rfl⟩, -⟩ := GlobalTheory.SmGL.mem_iwahori.1 hg
  exact (h.val i j).2
end GlobalTheory.CompanionTheory.IwContract
