-- Prove2me | solution 1 for GlobalTheory.CuspGL.CyclicMass.charpoly_mulLeft_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:02:47.040802+00:00
-- url     : https://prove2.me/submissions/6a7460bc-8538-42fa-8556-d27d9763cb70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.CyclicMass
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL.CyclicMass
theorem _root_.solution (D : F[X]) (hD : D.Monic) [FiniteDimensional F (AdjoinRoot D)] :
    LinearMap.charpoly (LinearMap.mulLeft F (AdjoinRoot.root D)) = D := by
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hD)
  rw [AdjoinRoot.powerBasis'_gen] at h
  have h2 : minpoly F (AdjoinRoot.root D) = D := by
    rw [AdjoinRoot.minpoly_root hD.ne_zero, hD.leadingCoeff]; simp
  rw [h2] at h
  rw [← LinearMap.charpoly_toMatrix _ (AdjoinRoot.powerBasis' hD).basis]
  exact h
end GlobalTheory.CuspGL.CyclicMass
