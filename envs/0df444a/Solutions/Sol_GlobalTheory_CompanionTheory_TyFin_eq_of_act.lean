-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.eq_of_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:10.220925+00:00
-- url     : https://prove2.me/submissions/fc3fe221-f846-4f5f-bc57-7b3ecd66e578

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentAction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentProperties
import Theorems.Thm_GlobalTheory_T_separable_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution (x y : MonoidAlgebra ℂ Γ)
    (h : ∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = Representation.asAlgebraHom τ.ρ y) :
    x = y :=
  sub_eq_zero.1 (GlobalTheory.T.separable_irreducible Γ _ fun τ hτ => by rw [map_sub, h τ hτ, sub_self])
end GlobalTheory.CompanionTheory.TyFin
