-- Prove2me | solution 1 for GlobalTheory.T.isSemisimple_of_locallyFinite_compactGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:44.807567+00:00
-- url     : https://prove2.me/submissions/e7823a0a-e74d-4df0-95aa-4499275e6c36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroupStatement
import Theorems.Thm_GlobalTheory_LocFinSemisimple_semisimple_of_locallyFinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) → ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  first | exact @GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite | exact GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite | (intros; apply GlobalTheory.LocFinSemisimple.semisimple_of_locallyFinite <;> assumption)
end _root_.GlobalTheory.T
