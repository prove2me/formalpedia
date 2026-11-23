-- Prove2me | solution 1 for GlobalTheory.FiniteAbelianWeights.avg_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:27.807983+00:00
-- url     : https://prove2.me/submissions/e93910c5-9a0f-40ab-881f-d945a877faa9

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
theorem _root_.solution (hu : u * (Fintype.card T : o) = 1) (c : T →* oˣ) (x : M)
    (hx : ∀ t, ρ t x = (c t : o) • x) : avg ρ u c x = x := by
  simp only [avg_apply, hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul o, smul_smul, hu, one_smul]
end GlobalTheory.FiniteAbelianWeights
