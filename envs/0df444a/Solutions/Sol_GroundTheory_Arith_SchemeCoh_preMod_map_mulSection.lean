-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.preMod_map_mulSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:16:25.166893+00:00
-- url     : https://prove2.me/submissions/1fdede12-b032-4004-ade2-3469c6bba388

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SectionTensor
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_preMod_map_homOfPreMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct
universe u
noncomputable section
variable {X : Scheme.{u}}
variable (M L : X.Modules) (s : Γ(L, ⊤))
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution :
    (preMod X).map (mulSection M L s) = tensorSection M L s ≫ tensorToSheaf M L :=
  preMod_map_homOfPreMod _
end GroundTheory.Arith.SchemeCoh
