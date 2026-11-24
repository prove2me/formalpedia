-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.mem_span_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:50.99489+00:00
-- url     : https://prove2.me/submissions/9af09909-c0c0-4ab9-ade8-17ab77ece9be

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero
namespace GlobalTheory.SS.DefectZero
theorem _root_.solution {A D K M I : Type} [CommRing A] [CommRing D] [CommRing K] [Algebra A D]
    [Algebra D K] [Algebra A K] [IsScalarTower A D K] [AddCommGroup M] [Module A M] (g : I → M)
    (m : M) (h : (1 : D) ⊗ₜ[A] m ∈ Submodule.span D (Set.range fun j => (1 : D) ⊗ₜ[A] g j)) :
    (1 : K) ⊗ₜ[A] m ∈ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] g j) := by
  let ρ : D ⊗[A] M →ₗ[D] K ⊗[A] M := AlgebraTensorModule.rTensor A M (Algebra.linearMap D K)
  have h1 := Submodule.mem_map_of_mem (f := ρ) h
  rw [Submodule.map_span, ← Set.range_comp] at h1
  have h2 := Submodule.span_le_restrictScalars D K _ h1
  simpa [ρ, Function.comp_def] using h2
end GlobalTheory.SS.DefectZero
