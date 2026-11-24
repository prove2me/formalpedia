-- Prove2me | solution 1 for GlobalTheory.IrredSB.modul_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:53.907985+00:00
-- url     : https://prove2.me/submissions/3c8b8d22-bbf6-4ee9-9be2-8e8babc97972

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Theorems.Thm_GlobalTheory_IrredSB_char_isLocallyConstant

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
namespace GlobalTheory.IrredSB
theorem _root_.solution (ψk : AddChar k Circle) (hψ : Continuous ψk) {Φ : Matrix Y Y' k → ℂ}
    (hΦ : Φ ∈ SB (Matrix Y Y' k)) (b : Matrix Y Y' k) :
    (fun t => (ψk (pair b t) : ℂ) * Φ t) ∈ SB (Matrix Y Y' k) := by
  have hp : Continuous (fun t : Matrix Y Y' k => pair b t) :=
    continuous_finset_sum _ fun r _ => continuous_finset_sum _ fun q _ =>
      continuous_const.mul (continuous_id.matrix_elem r q)
  have hl : IsLocallyConstant (fun t => (ψk (pair b t) : ℂ)) :=
    ((char_isLocallyConstant ψk hψ).comp_continuous hp).comp (fun z : Circle => (z : ℂ))
  exact ⟨hl.mul hΦ.1, HasCompactSupport.mul_left (f := fun t => (ψk (pair b t) : ℂ)) hΦ.2⟩
end GlobalTheory.IrredSB
