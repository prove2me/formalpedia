-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilOneMember.isHerm_dbl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:40:56.734572+00:00
-- url     : https://prove2.me/submissions/d208a945-3689-4d0c-8041-e31b7a68034f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DblCoordUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilOneMember
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.WeilOneMember
theorem _root_.solution {JB : Matrix β β E} (h : IsHerm c JB) : IsHerm c (dbl JB) := by
  obtain ⟨hs, hu⟩ := h
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) <;> simp [dbl, hs]
  · rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact hu.mul ((isUnit_neg_one.pow _).mul hu)
end GlobalTheory.CompanionTheory.WeilOneMember
