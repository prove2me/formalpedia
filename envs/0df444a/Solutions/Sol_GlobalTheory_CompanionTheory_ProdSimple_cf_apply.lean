-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSimple.cf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:09.51153+00:00
-- url     : https://prove2.me/submissions/7c58cf41-e629-4c8e-8a37-8a2521af604d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSimple
namespace GlobalTheory.CompanionTheory.ProdSimple
theorem _root_.solution {Γ : Type} [Group Γ] (g : Γ) (a : MonoidAlgebra ℂ Γ) : cf g a = a.coeff g := rfl
end GlobalTheory.CompanionTheory.ProdSimple
