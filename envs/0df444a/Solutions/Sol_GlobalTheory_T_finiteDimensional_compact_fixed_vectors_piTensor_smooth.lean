-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:09.975917+00:00
-- url     : https://prove2.me/submissions/f91cf5ea-dcf1-4854-a49b-482bc9b761e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalCompactFixedVectorsPiTensorSmoo
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalCompactFixedVectorsPiTensorSmooStatement
import Theorems.Thm_GlobalTheory_PiTensorFixed_finiteDimensional_fixed_piTensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)), (∀ a, IsSmooth (ρ a)) → ∀ (K : ∀ a, Subgroup (Γ a)), (∀ a, IsCompact (K a : Set (Γ a))) → (∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) → FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) := by
  first | exact @GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor | exact GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor | (intros; apply GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor <;> assumption)
end _root_.GlobalTheory.T
