-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.Cov.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:19.782217+00:00
-- url     : https://prove2.me/submissions/93a3643d-9cf8-4bfb-918b-a29ece404a1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
namespace GlobalTheory.SS.Smoothening
namespace Cov
theorem _root_.solution {E : Pts R B} {E' : Pts R C} (φ : B →ₐ[R] C) (ho : GenOpen K φ) (h' : Cov K E')
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a →
      ∃ a' : C →ₐ[R] R', a'.comp φ = a ∧ E' R' a') : Cov K E := by
  obtain ⟨l, p, q⟩ := h'
  refine ⟨l.map fun x => ⟨x.1, x.2.comp φ⟩, fun x hx => ?_, fun R' _ _ a ha => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨(p y hy).1, ho.comp (p y hy).2⟩
  · obtain ⟨a', rfl, ha'⟩ := h R' a ha
    obtain ⟨x, hx, b, rfl⟩ := q R' a' ha'
    exact ⟨_, List.mem_map_of_mem hx, b, rfl⟩
end Cov
end GlobalTheory.SS.Smoothening
