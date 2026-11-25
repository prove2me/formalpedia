-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup.psiZero_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:46.747972+00:00
-- url     : https://prove2.me/submissions/5f95732d-b223-49df-bb1b-4abb413506ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) (u : 𝒪[k]) :
    psiZero hψ hϖ (IsLocalRing.residue 𝒪[k] u) = ψ ((u : k) / ϖ) :=
  psi_congr hψ hϖ (Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k])) _)
end GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
