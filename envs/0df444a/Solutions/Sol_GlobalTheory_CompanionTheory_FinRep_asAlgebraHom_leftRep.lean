-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinRep.asAlgebraHom_leftRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:23.768734+00:00
-- url     : https://prove2.me/submissions/4287bd47-c9fb-4051-b7c3-65e83bb28fd0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible
import Theorems.Thm_GlobalTheory_CompanionTheory_FinRep_leftRep_apply

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
theorem _root_.solution (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ))
    (x : MonoidAlgebra ℂ Γ) (n : N) : Representation.asAlgebraHom (leftRep N) x n = x • n := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simp [Representation.asAlgebraHom_of, leftRep_apply]
  | add a b ha hb => simp [map_add, add_smul, ha, hb]
  | smul c a ha => simp [map_smul, ha]
end GlobalTheory.CompanionTheory.FinRep
