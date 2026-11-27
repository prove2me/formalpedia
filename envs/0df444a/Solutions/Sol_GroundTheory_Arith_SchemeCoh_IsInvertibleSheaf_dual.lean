-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:46.832895+00:00
-- url     : https://prove2.me/submissions/91125c24-28b0-4da0-ae1d-56399b54d69d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_DualSec_isBasisOn_dualBasis
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
namespace IsInvertibleSheaf
theorem _root_.solution {M : X.Modules} (hM : IsInvertibleSheaf M) :
    IsInvertibleSheaf (dualSheaf M) := by
  intro x
  obtain ⟨U, hx, s, hs⟩ := hM x
  exact ⟨U, hx, _, (DualSec.isBasisOn_dualBasis hs).map_of_alt (dualIsoHom M)
    (MorphismProperty.of_isIso _ _)⟩
end IsInvertibleSheaf
end GroundTheory.Arith.SchemeCoh
