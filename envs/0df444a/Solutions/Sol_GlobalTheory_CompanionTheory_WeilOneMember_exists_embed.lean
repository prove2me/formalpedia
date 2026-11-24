-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilOneMember.exists_embed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:30.960804+00:00
-- url     : https://prove2.me/submissions/0cc1c172-f737-4306-9b24-6d4bf9d9ade2

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
theorem _root_.solution {JB : Matrix β β E} (g : UG c JB) : ∃ gd : UG c (dbl JB),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  let G : GL β E := g
  let M : GL (β ⊕ β) E :=
    ⟨Matrix.fromBlocks (G : Matrix β β E) 0 0 1, Matrix.fromBlocks ((G⁻¹ : GL β E) : Matrix β β E) 0 0 1,
      by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
  have hg : (G : Matrix β β E).transpose * JB * (G : Matrix β β E).map c = JB := g.2
  have hM : M ∈ UG c (dbl JB) := by
    show (M : Matrix (β ⊕ β) (β ⊕ β) E).transpose * dbl JB * (M : Matrix (β ⊕ β) (β ⊕ β) E).map c = dbl JB
    simp only [M, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.transpose_zero, Matrix.transpose_one, Matrix.map_zero _ (map_zero c), Matrix.map_one _ (map_zero c) (map_one c)]
    simp [hg]
  exact ⟨⟨M, hM⟩, rfl⟩
end GlobalTheory.CompanionTheory.WeilOneMember
