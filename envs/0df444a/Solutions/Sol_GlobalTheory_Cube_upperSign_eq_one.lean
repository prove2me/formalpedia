-- Prove2me | solution 1 for GlobalTheory.Cube.upperSign_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:40:44.022556+00:00
-- url     : https://prove2.me/submissions/f07df01d-cd0b-46e0-9ae3-0a6338e6f41c

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
theorem _root_.solution (h : ∀ k, e k < i) (s : Finset κ) : upperSign e i s = 1 := by
  have : (insert i (s.map e.toEmbedding)).filter (· < i) = s.map e.toEmbedding := by
    rw [Finset.filter_insert, if_neg (lt_irrefl i), Finset.filter_true_of_mem]
    intro j hj
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hj
    exact h k
  rw [upperSign, cubeSign, this, Finset.card_map, ← mul_pow]; simp
end GlobalTheory.Cube
