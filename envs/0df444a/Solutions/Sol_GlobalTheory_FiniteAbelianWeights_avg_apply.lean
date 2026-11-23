-- Prove2me | solution 1 for GlobalTheory.FiniteAbelianWeights.avg_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:28.923823+00:00
-- url     : https://prove2.me/submissions/e8650afd-5ed1-4939-9111-5d68205d1457

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
variable [Fintype T] (ρ : Representation o T M) (u : o)
namespace GlobalTheory.FiniteAbelianWeights
theorem _root_.solution (c : T →* oˣ) (x : M) :
    avg ρ u c x = u • ∑ t : T, (((c t)⁻¹ : oˣ) : o) • ρ t x := by
  simp [avg, LinearMap.sum_apply]
end GlobalTheory.FiniteAbelianWeights
