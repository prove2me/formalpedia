-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordInhab.span_two_three
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:46.00773+00:00
-- url     : https://prove2.me/submissions/279a8d38-4d6a-4fc0-9a4b-b0b86ddcc4a7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory CptModel
open CoordInhab
open GlobalTheory.CompanionTheory.Ar.CoordInhab
namespace GlobalTheory.CompanionTheory.Ar.CoordInhab
theorem _root_.solution : Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h2 : (2 : ℤ) ∈ Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)) :=
    Ideal.subset_span ⟨0, by simp⟩
  have h3 : (3 : ℤ) ∈ Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)) :=
    Ideal.subset_span ⟨1, by simp⟩
  have e : (1 : ℤ) = 3 - 2 := by norm_num
  rw [e]
  exact Ideal.sub_mem _ h3 h2
end GlobalTheory.CompanionTheory.Ar.CoordInhab
