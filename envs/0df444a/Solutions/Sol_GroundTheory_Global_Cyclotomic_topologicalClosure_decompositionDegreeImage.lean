-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.topologicalClosure_decompositionDegreeImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:53.263295+00:00
-- url     : https://prove2.me/submissions/78d598df-5669-450e-9bc5-f51f2f0e1344

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isClosed_decompositionDegreeImage

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
variable (q : Nat.Primes) (P : Ideal (𝓞 ℚ̄))
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution :
    (decompositionDegreeImage P).topologicalClosure = decompositionDegreeImage P :=
  SetLike.coe_injective (by
    rw [AddSubgroup.topologicalClosure_coe, (isClosed_decompositionDegreeImage P).closure_eq])
end GroundTheory.Global.Cyclotomic
