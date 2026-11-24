-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinRep.leftRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:40.464554+00:00
-- url     : https://prove2.me/submissions/ad517342-4433-43a0-b87e-1fbd4621664f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinRep
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.FinRep
theorem _root_.solution (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) (g : Γ) (n : N) :
    leftRep N g n = MonoidAlgebra.of ℂ Γ g • n := rfl
end GlobalTheory.CompanionTheory.FinRep
