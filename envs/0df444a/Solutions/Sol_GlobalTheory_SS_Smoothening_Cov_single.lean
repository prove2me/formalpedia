-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.Cov.single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:57.820178+00:00
-- url     : https://prove2.me/submissions/ec280570-52fd-4176-9974-a2737c03322f

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
theorem _root_.solution {E : Pts R B} (φ : B →ₐ[R] C) (hs : Algebra.Smooth R C) (ho : GenOpen K φ)
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → ∃ a' : C →ₐ[R] R', a'.comp φ = a) : Cov K E :=
  ⟨[⟨CommAlgCat.of R C, φ⟩], fun x hx => by
    obtain rfl := List.mem_singleton.1 hx
    exact ⟨hs, ho⟩, fun R' _ _ a ha => ⟨_, List.mem_singleton_self _, h R' a ha⟩⟩
end Cov
end GlobalTheory.SS.Smoothening
