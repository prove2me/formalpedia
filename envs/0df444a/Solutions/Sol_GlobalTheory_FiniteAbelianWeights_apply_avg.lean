-- Prove2me | solution 1 for GlobalTheory.FiniteAbelianWeights.apply_avg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:49.092133+00:00
-- url     : https://prove2.me/submissions/6419d00b-bc4a-49ff-b917-a3cbc4a0cfd5

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
theorem _root_.solution (c : T →* oˣ) (s : T) (x : M) :
    ρ s (avg ρ u c x) = (c s : o) • avg ρ u c x := by
  simp only [avg_apply, map_smul, map_sum]
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
  congr 1
  rw [← Units.val_mul]
  congr 1
  rw [mul_inv, mul_inv_cancel_left]
end GlobalTheory.FiniteAbelianWeights
