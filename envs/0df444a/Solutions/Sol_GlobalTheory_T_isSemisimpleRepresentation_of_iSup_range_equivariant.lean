-- Prove2me | solution 1 for GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:21.264323+00:00
-- url     : https://prove2.me/submissions/5521cb20-ff7a-4c5e-a69e-5a2f4264bd0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationOfISupRangeEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationOfISupRangeEquivariantStatement
import Theorems.Thm_GlobalTheory_ClassFin_isSemisimpleRepresentation_of_iSup_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range <;> assumption)
end _root_.GlobalTheory.T
