-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.coordTie_two_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:45.907098+00:00
-- url     : https://prove2.me/submissions/e42afd7b-f51f-41be-98f7-1f3cf3869ea0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_coordTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
variable [IsDomain A] [IsFractionRing A Ω]
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution : CoordTie ℤ (gen ℤ ℚ) (fun j => algebraMap ℤ ℚ (![2, 3] j)) := by
  refine coordTie ℤ ℚ ℤ ?_ fun c _ a => Subalgebra.algebraMap_mem _ a
  rw [Ideal.eq_top_iff_one]
  have h := Ideal.sub_mem (Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)))
    (Ideal.subset_span ⟨1, rfl⟩) (Ideal.subset_span ⟨0, rfl⟩)
  simpa using h
end GlobalTheory.CompanionTheory.Ar.CoordModel
