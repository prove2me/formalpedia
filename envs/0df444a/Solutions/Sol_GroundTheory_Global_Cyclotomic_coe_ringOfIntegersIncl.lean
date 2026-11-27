-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.coe_ringOfIntegersIncl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:21.22799+00:00
-- url     : https://prove2.me/submissions/213df72d-c6ea-412b-80f7-11e1a87c4f26

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (L : IntermediateField ℚ ℚ̄) (a : 𝓞 L) :
    ((ringOfIntegersIncl L a : 𝓞 ℚ̄) : ℚ̄) = ((a : L) : ℚ̄) :=
  rfl
end GroundTheory.Global.Cyclotomic
