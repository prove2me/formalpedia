-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.infinite_decompositionComponentImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:22.057375+00:00
-- url     : https://prove2.me/submissions/72e7ba78-e5ce-4338-a32d-67b8f9e92644

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_decompositionComponentImage_ne_zero
import Theorems.Thm_GroundTheory_Global_Cyclotomic_infinite_of_ne_zero


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
theorem _root_.solution (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (decompositionComponentImage q P : Set ℤ_[q]).Infinite := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_decompositionComponentImage_ne_zero q P p
  exact infinite_of_ne_zero _ hx hx0
end GroundTheory.Global.Cyclotomic
