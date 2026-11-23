-- Prove2me | solution 1 for GlobalTheory.ExtDescent.fpqc_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:02.263426+00:00
-- url     : https://prove2.me/submissions/e85708af-413d-487a-b92b-69f61b7eece2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescends

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
open GlobalTheory GlobalTheory.ExtDescent
variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}
namespace GlobalTheory.ExtDescent
theorem _root_.solution [Flat f] [Surjective f] [QuasiCompact f] {X X₀ : Scheme.{0}} {p : X ⟶ X₀}
    {s : X ⟶ S} {s₀ : X₀ ⟶ S₀} (h : IsPullback p s s₀ f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) p :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›,
    MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip ‹_›⟩
end GlobalTheory.ExtDescent
