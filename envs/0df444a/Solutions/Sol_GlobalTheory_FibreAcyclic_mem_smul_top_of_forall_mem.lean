-- Prove2me | solution 1 for GlobalTheory.FibreAcyclic.mem_smul_top_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:49.140065+00:00
-- url     : https://prove2.me/submissions/f328ae54-fc4f-46c2-b173-ae0ca4e48e5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]
omit [IsLocalRing R]
namespace GlobalTheory.FibreAcyclic
theorem _root_.solution (N : Ideal R) {F : Type} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] (f : Module.Dual R F) (hf : ∀ x, f x ∈ N) : f ∈ N • (⊤ : Submodule R (Module.Dual R F)) := by
  classical
  rw [← (Module.Free.chooseBasis R F).sum_dual_apply_smul_coord f]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hf _) trivial
end GlobalTheory.FibreAcyclic
