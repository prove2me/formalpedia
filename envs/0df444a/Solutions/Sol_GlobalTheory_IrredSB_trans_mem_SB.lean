-- Prove2me | solution 1 for GlobalTheory.IrredSB.trans_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:05.484971+00:00
-- url     : https://prove2.me/submissions/1d44b5d2-3e9b-448e-af4a-aebed79658c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [Fintype Y']
omit [Fintype Y] [Fintype Y']
namespace GlobalTheory.IrredSB
theorem _root_.solution {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (x : Matrix Y Y' k) :
    (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) :=
  ⟨hΦ.1.comp_continuous (f := fun t => t + x) (by fun_prop), hΦ.2.comp_homeomorph (Homeomorph.addRight x)⟩
end GlobalTheory.IrredSB
