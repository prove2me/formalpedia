-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isOpen_stabilizer_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:15.128114+00:00
-- url     : https://prove2.me/submissions/6253be74-c008-42d6-a81f-9e4d9edb558d

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
theorem _root_.solution (b : 𝓞 ℚ̄) :
    IsOpen (MulAction.stabilizer Gal(ℚ̄/ℚ) b : Set Gal(ℚ̄/ℚ)) := by
  have : FiniteDimensional ℚ ℚ⟮(b : ℚ̄)⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  refine Subgroup.isOpen_mono (H₁ := (ℚ⟮(b : ℚ̄)⟯).fixingSubgroup) (fun σ hσ => ?_)
    (ℚ⟮(b : ℚ̄)⟯).fixingSubgroup_isOpen
  rw [MulAction.mem_stabilizer_iff]
  exact RingOfIntegers.ext ((mem_fixingSubgroup_iff _ σ).mp hσ (b : ℚ̄) (mem_adjoin_simple_self ℚ _))
end GroundTheory.Global.Cyclotomic
