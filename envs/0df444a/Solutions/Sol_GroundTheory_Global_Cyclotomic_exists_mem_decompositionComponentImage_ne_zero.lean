-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_mem_decompositionComponentImage_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:06:50.117261+00:00
-- url     : https://prove2.me/submissions/eca89d95-f202-4a5d-b8a1-bef1724b4e57

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_degreeComponent_ne_one

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
    ∃ x ∈ decompositionComponentImage q P, x ≠ 0 := by
  obtain ⟨σ, hσ, hne⟩ := exists_mem_stabilizer_degreeComponent_ne_one (p := p) P q
  refine ⟨_, ⟨σ, hσ, rfl⟩, fun h => hne ?_⟩
  have h' : Multiplicative.toAdd (degreeComponent q σ) = 0 := h
  rw [← ofAdd_toAdd (degreeComponent q σ), h', ofAdd_zero]
end GroundTheory.Global.Cyclotomic
