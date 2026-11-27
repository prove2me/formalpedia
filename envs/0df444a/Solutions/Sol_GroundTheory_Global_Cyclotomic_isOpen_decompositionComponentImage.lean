-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isOpen_decompositionComponentImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:23.053883+00:00
-- url     : https://prove2.me/submissions/c89775c0-3be2-478e-9d0f-f82c0202094e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isClosed_decompositionComponentImage
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_decompositionComponentImage_ne_zero
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isOpen_of_isClosed_of_ne_zero


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
    IsOpen (decompositionComponentImage q P : Set ℤ_[q]) := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_decompositionComponentImage_ne_zero q P p
  exact isOpen_of_isClosed_of_ne_zero _ (isClosed_decompositionComponentImage q P) hx hx0
end GroundTheory.Global.Cyclotomic
