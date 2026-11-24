-- Prove2me | solution 1 for GlobalTheory.IrredSBVec.continuous_toCircle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:07.273049+00:00
-- url     : https://prove2.me/submissions/986664bc-69ef-4529-8ea7-51c676ae5378

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatVectorIrreducibleTranslationsChara

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IrredSBVec
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IrredSBVec
theorem _root_.solution (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (hψ : Continuous ψ0) :
    Continuous (toCircle ψ0 h1) :=
  hψ.subtype_mk _
end GlobalTheory.IrredSBVec
