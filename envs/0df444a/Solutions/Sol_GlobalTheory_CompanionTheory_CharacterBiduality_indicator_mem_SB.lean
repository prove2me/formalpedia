-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharacterBiduality.indicator_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:38.692082+00:00
-- url     : https://prove2.me/submissions/5ab7eb1c-935c-424c-a4af-b0ad8b1be02d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharacterBiduality
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharacterBiduality
theorem _root_.solution {n : ℕ} (A : AddSubgroup (Fin n → k))
    (hAc : IsCompact (A : Set (Fin n → k))) (hAo : IsOpen (A : Set (Fin n → k))) :
    (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (Fin n → k) := by
  have hcl : IsClopen (A : Set (Fin n → k)) := ⟨AddSubgroup.isClosed_of_isOpen A hAo, hAo⟩
  exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩
end GlobalTheory.CompanionTheory.CharacterBiduality
