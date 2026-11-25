-- Prove2me | solution 1 for GlobalTheory.Cube.upperSign_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:49.189868+00:00
-- url     : https://prove2.me/submissions/22ce3722-9812-4332-a80d-a94348232299

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
variable (e : κ ↪o ι) (i : ι)
namespace GlobalTheory.Cube
theorem _root_.solution (h : ∀ k, i ≤ e k) (s : Finset κ) :
    upperSign e i s = (-1) ^ s.card := by
  rw [upperSign, cubeSign_eq_one_of_forall_le, mul_one]
  intro j hj
  rcases Finset.mem_insert.1 hj with rfl | hj
  · exact le_rfl
  · obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hj
    exact h k
end GlobalTheory.Cube
