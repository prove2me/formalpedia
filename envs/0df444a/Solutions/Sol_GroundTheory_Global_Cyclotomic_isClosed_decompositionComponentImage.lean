-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isClosed_decompositionComponentImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:37:58.497356+00:00
-- url     : https://prove2.me/submissions/90d41e88-80ba-4550-bd7d-d83546435fdd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isClosed_stabilizer
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_degreeComponent


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
    IsClosed (decompositionComponentImage q P : Set ℤ_[q]) :=
  ((isClosed_stabilizer P).isCompact.image
    (continuous_toAdd.comp (continuous_degreeComponent q))).isClosed
end GroundTheory.Global.Cyclotomic
