-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:23:26.116311+00:00
-- url     : https://prove2.me/submissions/2d3d700e-f031-4b1b-9778-98d571b436ae

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_iso

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
theorem _root_.solution {M N : X.Modules} (e : M ≅ N) (hM : IsInvertibleSheaf M) :
    IsInvertibleSheaf N := by
  intro x
  obtain ⟨U, hx, s, hs⟩ := hM x
  exact ⟨U, hx, _, hs.map_iso e⟩
end IsInvertibleSheaf
end GroundTheory.Arith.SchemeCoh
