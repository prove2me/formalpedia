-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.nonempty_iso_iff_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:56.474953+00:00
-- url     : https://prove2.me/submissions/cb18fe33-6bfc-41f8-82ff-fc6ca7e4f120

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentAction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentProperties
import Theorems.Thm_GlobalTheory_T_simple_iff_irreducible


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
theorem _root_.solution (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ Nonempty (Representation.Equiv τ.ρ σ.ρ) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 Γ τ σ]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun v => he g v⟩
  · rintro ⟨φ⟩
    exact ⟨φ.toLinearEquiv, fun γ v => LinearMap.congr_fun (φ.isIntertwining' γ) v⟩
end GlobalTheory.CompanionTheory.TyFin
