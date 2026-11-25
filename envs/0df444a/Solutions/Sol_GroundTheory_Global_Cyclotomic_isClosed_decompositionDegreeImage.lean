-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isClosed_decompositionDegreeImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:07:00.198174+00:00
-- url     : https://prove2.me/submissions/d24eca20-a752-47f7-b47f-4f82c14b1c67

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isClosed_stabilizer
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_degree


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
    IsClosed (decompositionDegreeImage P : Set ℤ̂) :=
  ((isClosed_stabilizer P).isCompact.image (continuous_toAdd.comp continuous_degree)).isClosed
end GroundTheory.Global.Cyclotomic
