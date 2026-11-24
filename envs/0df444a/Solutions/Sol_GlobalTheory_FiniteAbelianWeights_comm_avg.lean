-- Prove2me | solution 1 for GlobalTheory.FiniteAbelianWeights.comm_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:07:59.768214+00:00
-- url     : https://prove2.me/submissions/1df13e18-1719-4e56-8f95-66919d0ee143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open TensorProduct
open GlobalTheory
open GlobalTheory.FiniteAbelianWeights
variable {o : Type} [CommRing o] {T : Type} [CommGroup T]
  {M : Type} [AddCommGroup M] [Module o M]
variable [Fintype T] (ρ : Representation o T M) (u : o)
namespace GlobalTheory.FiniteAbelianWeights
theorem _root_.solution (c : T →* oˣ) (s : T) (x : M) : ρ s (avg ρ u c x) = avg ρ u c (ρ s x) := by
  simp only [avg_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Module.End.mul_apply, ← map_mul, mul_comm s t, map_mul, Module.End.mul_apply]
end GlobalTheory.FiniteAbelianWeights
