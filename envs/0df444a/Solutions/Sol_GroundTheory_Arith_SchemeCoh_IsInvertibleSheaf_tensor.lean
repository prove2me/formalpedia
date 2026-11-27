-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:08.971832+00:00
-- url     : https://prove2.me/submissions/7b8212be-fbd7-4f9c-90d6-6beef5a14a32

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_W_tensorToSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_of_alt
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_restrict
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_tmul

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
theorem _root_.solution {M N : X.Modules} (hM : IsInvertibleSheaf M)
    (hN : IsInvertibleSheaf N) : IsInvertibleSheaf (M ⊗ N) := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hM x
  obtain ⟨V, hxV, t, ht⟩ := hN x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, _, ((hs.restrict inf_le_left).tmul (ht.restrict inf_le_right)).map_of_alt
    (tensorToSheaf M N) (W_tensorToSheaf M N)⟩
end IsInvertibleSheaf
end GroundTheory.Arith.SchemeCoh
