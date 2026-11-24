-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.injective_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:33:57.361886+00:00
-- url     : https://prove2.me/submissions/b85af144-7f89-4a8d-ae22-91e68265982d

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
import Theorems.Thm_GlobalTheory_SS_DefectZero_span_one_tmul

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
theorem _root_.solution (R A C k I : Type) [CommRing R] [CommRing A] [CommRing C]
    [Field k] [Algebra R A] [Algebra A C] [Algebra C k] [Algebra A k] [IsScalarTower A C k]
    (f : I → A) (hf : RingHom.ker (algebraMap A C) = Ideal.span (Set.range f))
    (hl : LinearIndependent k fun j => (1 : k) ⊗ₜ[A] KaehlerDifferential.D R A (f j)) :
    Function.Injective (cotangentComplexBaseChange R C A k) := by
  let g : I → RingHom.ker (algebraMap A C) := fun j => ⟨f j, hf.ge (Ideal.subset_span ⟨j, rfl⟩)⟩
  have hg : Submodule.span A (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective (RingHom.ker (algebraMap A C)).injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hf.symm
  refine LinearMap.injective_of_linearIndependent (span_one_tmul g hg) ?_
  simpa [Function.comp_def, cotangentComplexBaseChange_tmul, g] using hl
end GlobalTheory.SS.DefectZero
