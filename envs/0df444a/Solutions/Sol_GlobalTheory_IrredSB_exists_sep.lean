-- Prove2me | solution 1 for GlobalTheory.IrredSB.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:00.949069+00:00
-- url     : https://prove2.me/submissions/f3786b6a-2ee1-4515-ae4f-23f5d5fa46ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Theorems.Thm_GlobalTheory_CharDualMat_mem_integer_of_dual


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
namespace GlobalTheory.IrredSB
theorem _root_.solution (ψk : AddChar k Circle) (hψ : Continuous ψk) (h1 : ψk ≠ 1) {x : k} (hx : x ∉ 𝒪[k]) :
    ∃ b : k, (∀ u ∈ 𝒪[k], ψk (b * u) = 1) ∧ ψk (b * x) ≠ 1 := by
  by_contra h
  push Not at h
  exact hx (GlobalTheory.CharDualMat.mem_integer_of_dual ψk hψ h1 x h)
end GlobalTheory.IrredSB
