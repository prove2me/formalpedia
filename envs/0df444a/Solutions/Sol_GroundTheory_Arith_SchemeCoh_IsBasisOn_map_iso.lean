-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsBasisOn.map_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:53.450508+00:00
-- url     : https://prove2.me/submissions/9670f14d-354f-4ae0-a8e3-034a71a17d7c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_of_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
namespace IsBasisOn
theorem _root_.solution {M N : X.Modules} (e : M ≅ N) {U : X.Opens}
    {s : ((preMod X).obj M).obj (op U)} (hs : IsBasisOn ((preMod X).obj M) U s) :
    IsBasisOn ((preMod X).obj N) U (((preMod X).map e.hom).app _ s) :=
  hs.map_of_alt _ (MorphismProperty.of_isIso _ _)
end IsBasisOn
end GroundTheory.Arith.SchemeCoh
