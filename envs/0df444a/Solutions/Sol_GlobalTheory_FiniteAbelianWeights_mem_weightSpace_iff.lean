-- Prove2me | solution 1 for GlobalTheory.FiniteAbelianWeights.mem_weightSpace_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:18.482891+00:00
-- url     : https://prove2.me/submissions/c0d0b09e-d8dc-4aec-aafe-d1e96fe9bf4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition

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
namespace GlobalTheory.FiniteAbelianWeights
theorem _root_.solution {ι : Type} (f : ι → M →ₗ[o] M) (a : ι → o) (x : M) :
    x ∈ (⨅ t, LinearMap.ker (f t - a t • LinearMap.id)) ↔ ∀ t, f t x = a t • x := by
  simp [Submodule.mem_iInf, sub_eq_zero]
end GlobalTheory.FiniteAbelianWeights
