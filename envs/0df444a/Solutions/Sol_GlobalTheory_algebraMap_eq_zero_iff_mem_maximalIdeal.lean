-- Prove2me | solution 1 for GlobalTheory.algebraMap_eq_zero_iff_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:16.035383+00:00
-- url     : https://prove2.me/submissions/21ea6354-e850-40b2-9fb1-fe1d86f69256

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
universe u
variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [IsLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
omit [Algebra B W] [CommRing W]
namespace GlobalTheory
theorem _root_.solution (b : B) :
    algebraMap B K b = 0 ↔ b ∈ maximalIdeal B := by
  rw [IsScalarTower.algebraMap_apply B (ResidueField B) K, map_eq_zero]
  exact residue_eq_zero_iff b
end GlobalTheory
