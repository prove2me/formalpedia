-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.finiteType_lvl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:53:26.317202+00:00
-- url     : https://prove2.me/submissions/04c82881-28af-45c9-a25b-138cc63942b6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : S₀.Finite) (F : Finset R) : Algebra.FiniteType ℤ (lvl φ S₀ F) :=
  (Subalgebra.fg_iff_finiteType _).1
    (Subalgebra.fg_def.2 ⟨_, (hS₀.image φ).union F.finite_toSet, rfl⟩)
end GlobalTheory.CompanionTheory.Ultra
