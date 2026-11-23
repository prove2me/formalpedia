-- Prove2me | solution 1 for GlobalTheory.GlueModels.isOpenImmersion_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:32.059262+00:00
-- url     : https://prove2.me/submissions/a72577b6-a819-4314-834c-431b4185dc27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield

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
open GlobalTheory GlobalTheory.GlueModels
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GlueModels
theorem _root_.solution {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] : IsOpenImmersion (pushout.inl p q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.left))
end GlobalTheory.GlueModels
