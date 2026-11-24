-- Prove2me | solution 1 for GlobalTheory.addMonoidAlgebra_coboundary_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:07:19.111489+00:00
-- url     : https://prove2.me/submissions/708b5f17-67dd-4174-86d1-016a4adb1046

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Theorems.Thm_GlobalTheory_coboundary_apply_zero_left
import Theorems.Thm_GlobalTheory_finsupp_two_cocycle_eq_coboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
open GlobalTheory
variable {X : Type*} [Zero X] {A : Type*} [Ring A]
namespace GlobalTheory
theorem _root_.solution (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0)
    (g : A[X]) :
    mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f ↔ ∀ x, g.coeff x = f.coeff (0, x) := by
  refine ⟨fun h x => ?_, fun h => coeff_injective
    (finsupp_two_cocycle_eq_coboundary f.coeff (congrArg coeff hf) g.coeff h)⟩
  rw [← h]
  exact (coboundary_apply_zero_left g.coeff x).symm
end GlobalTheory
